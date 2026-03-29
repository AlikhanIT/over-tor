package main

/*
	tor-dl - fast large file downloader over locally installed Tor
	Copyright © 2025 Bryan Cuneo <https://github.com/BryanCuneo/tor-dl/>

	Based on torget by Michał Trojnara <https://github.com/mtrojnar/torget>

	This program is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License.

	This program is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with this program.  If not, see <https://www.gnu.org/licenses/>.
*/

import (
	"bufio"
	"context"
	"errors"
	"flag"
	"fmt"
	"io"
	"io/fs"
	"net"
	"net/http"
	"net/url"
	"os"
	"path/filepath"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"
)

// =============================================================
// ЛОКАЛЬНЫЙ КОНФИГ — просто меняй значения ниже
// =============================================================

// URL для скачивания. Если задан — CLI-аргумент игнорируется.
// Оставь "", чтобы передавать URL через командную строку.
var cfgURL = "https://nbg1-speed.hetzner.com/100MB.bin"

// Количество параллельных Tor-цепочек
var cfgCircuits = 20

// Папка назначения ("." = текущая директория)
var cfgDestination = "."

// Перезаписывать файл и создавать папки, если их нет
var cfgForce = false

// Минимальное время жизни цепочки (секунды)
var cfgMinLifetime = 10

// Принудительное имя выходного файла ("" = из URL)
var cfgName = ""

// Подавить обычный вывод (только ошибки)
var cfgQuiet = false

// Подавить весь вывод включая ошибки
var cfgSilent = false

// Порт Tor SOCKS-прокси
var cfgTorPort = 9050

// Подробный вывод диагностики
var cfgVerbose = false

// Разрешить HTTP (не рекомендуется)
var cfgAllowHTTP = false

// =============================================================

type chunk struct {
	start   int64
	length  int64
	circuit int
	bytes   int64
	since   time.Time
	cancel  context.CancelFunc
}

type State struct {
	ctx         context.Context
	src         string
	output      string
	bytesTotal  int64
	bytesPrev   int64
	circuits    int
	minLifetime time.Duration
	verbose     bool
	chunks      []chunk
	done        chan int
	log         chan string
	terminal    bool
	rwmutex     sync.RWMutex
}

const torBlock = 8000 // The longest plain text block in Tor

// Basic function to determine human-readable file sizes
func humanReadableSize(sizeInBytes float32) string {
	units := []string{"B", "KiB", "MiB", "GiB", "TiB"}
	i := 0

	for {
		if sizeInBytes >= 1024 && i < len(units) {
			sizeInBytes /= 1024
			i += 1
		} else {
			break
		}
	}

	return fmt.Sprintf("%.2f %s", sizeInBytes, units[i])
}

func httpClient(user string) *http.Client {
	proxyUrl, err := url.Parse(fmt.Sprintf("socks5://%s:%s@127.0.0.1:%d/", user, user, torPort))
	if err != nil {
		fmt.Fprintf(errorWriter, "ERROR - Failed to parse URL with user '%s' and port '%d'\n%v", user, torPort, err)
		os.Exit(1)
	}

	return &http.Client{
		Transport: &http.Transport{Proxy: http.ProxyURL(proxyUrl)},
	}
}

func NewState(ctx context.Context) *State {
	var s State
	s.circuits = circuits
	s.output = ""
	s.minLifetime = time.Duration(minLifetime) * time.Second
	s.verbose = verbose
	s.chunks = make([]chunk, s.circuits)
	s.ctx = ctx
	s.done = make(chan int)
	s.log = make(chan string, 10)
	st, _ := os.Stdout.Stat()
	s.terminal = st.Mode()&os.ModeCharDevice == os.ModeCharDevice

	return &s
}

func (s *State) printPermanent(txt string) {
	if s.terminal {
		fmt.Fprintf(messageWriter, "\r%-40s\n", txt)
	} else {
		fmt.Fprintln(messageWriter, txt)
	}
}

func (s *State) printTemporary(txt string) {
	if s.terminal {
		fmt.Fprintf(messageWriter, "\r%-40s", txt)
	}
}

func (s *State) chunkInit(id int) (client *http.Client, req *http.Request) {
	s.chunks[id].bytes = 0
	s.chunks[id].since = time.Now()
	ctx, cancel := context.WithCancel(s.ctx)
	s.chunks[id].cancel = cancel
	client = httpClient(fmt.Sprintf("tg%d", s.chunks[id].circuit))
	req, _ = http.NewRequestWithContext(ctx, "GET", s.src, nil)
	req.Header.Add("Range", fmt.Sprintf("bytes=%d-%d",
		s.chunks[id].start, s.chunks[id].start+s.chunks[id].length-1))
	return
}

func (s *State) chunkFetch(id int, client *http.Client, req *http.Request) {
	defer func() {
		s.done <- id
	}()

	if s.verbose {
		err := s.getExitNode(id, client)
		if err != nil {
			s.log <- fmt.Sprintf("getExitNode: %s", err.Error())
		}
	}

	resp, err := client.Do(req)
	if err != nil {
		s.log <- fmt.Sprintf("Client Do: %s", err.Error())
		return
	}
	if resp.Body == nil {
		s.log <- "Client Do: No response body"
		return
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusPartialContent {
		s.log <- fmt.Sprintf("Client Do: Unexpected HTTP status: %d", resp.StatusCode)
		return
	}

	// Open the output file
	file, err := os.OpenFile(s.output, os.O_WRONLY, 0)
	if err != nil {
		s.log <- fmt.Sprintf("os OpenFile: %s", err.Error())
		return
	}
	defer file.Close()

	_, err = file.Seek(s.chunks[id].start, io.SeekStart)
	if err != nil {
		s.log <- fmt.Sprintf("File Seek: %s", err.Error())
		return
	}

	// Copy network data to the output file
	buffer := make([]byte, torBlock)
	for {
		n, err := resp.Body.Read(buffer)
		if n > 0 {
			file.Write(buffer[:n])
			// Enough to RLock(), as we only modify our own chunk
			s.rwmutex.RLock()
			if int64(n) < s.chunks[id].length {
				s.chunks[id].start += int64(n)
				s.chunks[id].length -= int64(n)
				s.chunks[id].bytes += int64(n)
			} else {
				s.chunks[id].length = 0
			}
			s.rwmutex.RUnlock()
			if s.chunks[id].length == 0 {
				break
			}
		}
		if err != nil {
			s.log <- fmt.Sprintf("ReadCloser Read: %s", err.Error())
			break
		}
	}
}

func (s *State) getExitNode(id int, client *http.Client) error {
	req, _ := http.NewRequest(http.MethodGet, "https://check.torproject.org/api/ip", nil)

	resp, err := client.Do(req)
	if err != nil {
		return fmt.Errorf("client Do: %s", err.Error())
	}
	if resp.StatusCode != 200 {
		return fmt.Errorf("client Do: Unexpected HTTP status: %d", resp.StatusCode)
	}
	if resp.Body == nil {
		return fmt.Errorf("client Do: No response body")
	}
	defer resp.Body.Close()

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return fmt.Errorf("io ReadAll: %s", err.Error())
	}

	s.log <- fmt.Sprintf("Circuit #%d: Exit node: %s", id, body)
	return nil
}

func (s *State) printLogs() {
	n := len(s.log)
	logs := make([]string, n+1)
	for i := 0; i < n; i++ {
		logs[i] = <-s.log
	}
	logs[n] = "stop" // Not an expected log line
	sort.Strings(logs)
	prevLog := "start" // Not an expected log line
	cnt := 0
	for _, log := range logs {
		if log == prevLog {
			cnt++
		} else {
			if cnt > 0 {
				if cnt > 1 {
					prevLog = fmt.Sprintf("%s (%d times)", prevLog, cnt)
				}
				s.printPermanent(prevLog)
			}
			prevLog = log
			cnt = 1
		}
	}
}

func (s *State) ignoreLogs() {
	for len(s.log) > 0 {
		<-s.log
	}
}

func (s *State) statusLine() (status string) {
	// Calculate bytes transferred since the previous invocation
	var progressMessage string
	curr := s.bytesTotal

	s.rwmutex.RLock()
	for id := range s.circuits {
		curr -= s.chunks[id].length
	}
	s.rwmutex.RUnlock()

	if curr == s.bytesPrev {
		progressMessage = "stalled"
	} else {
		seconds := (s.bytesTotal - curr) / (curr - s.bytesPrev)
		progressMessage = fmt.Sprintf("%s/s, ETA %d:%02d:%02d",
			humanReadableSize(float32(curr-s.bytesPrev)),
			seconds/3600, seconds/60%60, seconds%60)
	}
	status = fmt.Sprintf("%6.2f%% done, %s",
		100*float32(curr)/float32(s.bytesTotal), progressMessage)

	s.bytesPrev = curr
	return
}

func (s *State) progress() {
	if s.verbose {
		s.printLogs()
	} else {
		s.ignoreLogs()
	}
	s.printTemporary(s.statusLine())
}

// Kill the worst performing circuit
func (s *State) darwin() {
	victim := -1
	var slowest float64
	now := time.Now()

	s.rwmutex.RLock()
	for id := range s.circuits {
		if s.chunks[id].cancel == nil {
			continue
		}
		eplased := now.Sub(s.chunks[id].since)
		if eplased < s.minLifetime {
			continue
		}
		throughput := float64(s.chunks[id].bytes) / eplased.Seconds()
		if victim >= 0 && throughput >= slowest {
			continue
		}
		victim = id
		slowest = throughput
	}
	if victim >= 0 {
		s.chunks[victim].cancel()
		s.chunks[victim].cancel = nil
	}
	s.rwmutex.RUnlock()
}

func (s *State) getOutputFilepath() {
	var filename string

	_, err := os.Stat(destination)
	if errors.Is(err, fs.ErrNotExist) {
		if force {
			os.MkdirAll(destination, os.ModePerm)
		} else {
			fmt.Fprintf(messageWriter, "WARNING: Unable to find destination \"%s\". Trying current directory instead.\n", destination)
			destination = "."
		}
	}

	// If no -name argument provided, extract the filename from the URL
	if name == "" {
		srcUrl, _ := url.Parse(s.src) // We've already parsed the URL, ignore errors here
		path := srcUrl.EscapedPath()
		slash := strings.LastIndex(path, "/")

		if slash >= 0 {
			filename = path[slash+1:]
		} else {
			filename = path
		}
		if filename == "" {
			filename = "index"
		}

		// Remove URL formatting (e.g. "%20" -> " ", "%C3" -> "ö")
		decoded, err := url.QueryUnescape(filename)
		if err != nil {
			fmt.Fprintf(messageWriter, "WARNING: Cannot decode \"%s\" - %v\n", filename, err)
		} else {
			filename = decoded
		}
	} else {
		filename = name
	}

	s.output = filepath.Join(destination, filename)
}
func renewTorCircuit() error {
	conn, err := net.Dial("tcp", "127.0.0.1:9051")
	if err != nil {
		return err
	}
	defer conn.Close()

	// если CookieAuth — можно без AUTH (зависит от конфига)
	_, err = fmt.Fprintf(conn, "AUTHENTICATE\r\n")
	if err != nil {
		return err
	}

	buf := make([]byte, 256)
	conn.Read(buf)

	_, err = fmt.Fprintf(conn, "SIGNAL NEWNYM\r\n")
	if err != nil {
		return err
	}

	conn.Read(buf)
	return nil
}
func isTorError(err error) bool {
	if err == nil {
		return false
	}

	msg := err.Error()

	return strings.Contains(msg, "EOF") ||
		strings.Contains(msg, "tls") ||
		strings.Contains(msg, "timeout") ||
		strings.Contains(msg, "connection reset") ||
		strings.Contains(msg, "x509")
}
func (s *State) headWithRetries(maxAttempts int) (*http.Response, error) {
	var lastErr error

	for attempt := 1; attempt <= maxAttempts; attempt++ {
		client := httpClient(fmt.Sprintf("tordl-head-%d", attempt))

		req, err := http.NewRequest("GET", s.src, nil)
		if err != nil {
			return nil, err
		}

		req.Header.Set("Range", "bytes=0-0")
		req.Header.Set("User-Agent", "Mozilla/5.0")
		req.Header.Set("Accept", "*/*")
		req.Header.Set("Connection", "keep-alive")

		resp, err := client.Do(req)
		if err != nil {
			lastErr = err

			if isTorError(err) {
				if s.verbose {
					s.log <- "Tor error detected, rotating circuit..."
				}
				_ = renewTorCircuit()
				time.Sleep(2 * time.Second)
			}

			time.Sleep(time.Duration(attempt) * 300 * time.Millisecond)
			continue
		}

		if resp.StatusCode != http.StatusOK && resp.StatusCode != http.StatusPartialContent {
			lastErr = fmt.Errorf("unexpected HTTP status: %d", resp.StatusCode)
			resp.Body.Close()

			_ = renewTorCircuit()
			continue
		}

		// 🔥 вытаскиваем реальный размер
		var size int64 = -1

		if cr := resp.Header.Get("Content-Range"); cr != "" {
			// bytes 0-0/123456
			if parts := strings.Split(cr, "/"); len(parts) == 2 {
				if v, err := strconv.ParseInt(parts[1], 10, 64); err == nil {
					size = v
				}
			}
		} else if resp.ContentLength > 0 {
			size = resp.ContentLength
		}

		if size <= 0 {
			lastErr = errors.New("failed to retrieve download length")
			resp.Body.Close()
			continue
		}

		// 💡 ВАЖНО: проставляем правильный размер
		resp.ContentLength = size

		// 💡 дочитываем и закрываем body (иначе утечки + keep-alive ломается)
		io.Copy(io.Discard, resp.Body)
		resp.Body.Close()

		return resp, nil
	}

	return nil, fmt.Errorf("HEAD request failed after %d attempts: %w", maxAttempts, lastErr)
}
func (s *State) Fetch(src string) int {
	var stop_status chan bool
	s.src = src
	startTime := time.Now()

	s.getOutputFilepath()
	// If the file already exists and the -force argument was not used, exit
	if _, err := os.Stat(s.output); err == nil && !force {
		fmt.Fprintf(errorWriter, "ERROR: \"%s\" already exists. Skipping.\n", s.output)
		return 1
	}
	fmt.Fprintf(messageWriter, "Output file:\t\t%s\n", s.output)

	// Get the target length with retries and circuit/IP rotation.
	resp, err := s.headWithRetries(10)
	if err != nil {
		fmt.Fprintf(errorWriter, "ERROR - Unable to prepare download over Tor: %v\n", err)
		return 1
	}
	if resp.Body != nil {
		resp.Body.Close()
	}
	s.bytesTotal = resp.ContentLength
	fmt.Fprintf(messageWriter, "Download filesize:\t%s\n", humanReadableSize(float32(s.bytesTotal)))

	// Create the output file. This will overwrite an existing file
	file, err := os.Create(s.output)
	if file != nil {
		file.Close()
	}
	if err != nil {
		fmt.Fprintln(messageWriter, err.Error())
		return 1
	}

	// Initialize chunks
	chunkLen := s.bytesTotal / int64(s.circuits)
	seq := 0
	for id := range s.circuits {
		s.chunks[id].start = int64(id) * chunkLen
		s.chunks[id].length = chunkLen
		s.chunks[id].circuit = seq
		seq++
	}
	s.chunks[s.circuits-1].length += s.bytesTotal % int64(s.circuits)

	// If not -quiet or -silent, update status message every 1 second
	if !quiet && !silent {
		stop_status = make(chan bool)
		go func() {
			for {
				time.Sleep(time.Second)

				select {
				case <-stop_status:
					close(stop_status)
					return
				default:
					s.progress()
				}
			}
		}()
	}

	// Spawn initial fetchers
	go func() {
		for id := range s.circuits {
			client, req := s.chunkInit(id)
			go s.chunkFetch(id, client, req)
			time.Sleep(499 * time.Millisecond) // Be gentle to the local tor daemon
		}
	}()

	// Spawn additional fetchers as needed
	for {
		select {
		case id := <-s.done:
			if s.chunks[id].length > 0 {
				// Error. Resume in a new and hopefully faster circuit
				s.chunks[id].circuit = seq
				seq++
			} else {
				// Completed
				longest := 0
				s.rwmutex.RLock()
				for i := 1; i < s.circuits; i++ {
					if s.chunks[i].length > s.chunks[longest].length {
						longest = i
					}
				}
				s.rwmutex.RUnlock()

				if s.chunks[longest].length == 0 {
					// All done
					howLong := time.Since(startTime)
					averageSpeed := humanReadableSize(float32(s.bytesTotal) / float32(howLong.Seconds()))

					// Clear progress, otherwise some text artifacts remain
					s.printTemporary(strings.Repeat(" ", 42))

					s.printPermanent(fmt.Sprintf("Download completed in:\t%s (%s/s)",
						howLong.Round(time.Second),
						averageSpeed))

					stop_status <- true
					return 0
				}
				if s.chunks[longest].length <= 5*torBlock {
					// Too short to split
					continue
				}

				// This circuit is faster, so we split 80%/20%
				s.rwmutex.Lock()
				s.chunks[id].length = s.chunks[longest].length * 4 / 5
				s.chunks[longest].length -= s.chunks[id].length
				s.chunks[id].start = s.chunks[longest].start + s.chunks[longest].length
				s.rwmutex.Unlock()
			}

			client, req := s.chunkInit(id)
			go s.chunkFetch(id, client, req)
		case <-time.After(time.Second * 30):
			s.darwin()
		}
	}
}

var allowHttp bool
var circuits int
var destination string
var force bool
var minLifetime int
var name string
var quiet bool
var silent bool
var torPort int
var verbose bool

var errorWriter io.Writer
var messageWriter io.Writer

func init() {
	// Применяем localDebug как дефолты для флагов.
	// Если задан localDebug.URL — CLI-аргументы URL не нужны.
	flag.BoolVar(&allowHttp, "allow-http", cfgAllowHTTP, "Allow tor-dl to download files over HTTP instead of HTTPS. Not recommended!")

	flag.IntVar(&circuits, "circuits", cfgCircuits, "Concurrent circuits.")
	flag.IntVar(&circuits, "c", cfgCircuits, "Concurrent circuits.")

	flag.StringVar(&destination, "destination", cfgDestination, "Output directory.")
	flag.StringVar(&destination, "d", cfgDestination, "Output directory.")

	flag.BoolVar(&force, "force", cfgForce, "Will create parent folder(s) and/or overwrite existing files.")

	flag.IntVar(&minLifetime, "min-lifetime", cfgMinLifetime, "Minimum circuit lifetime. (seconds)")
	flag.IntVar(&minLifetime, "l", cfgMinLifetime, "Minimum circuit lifetime. (seconds)")

	flag.StringVar(&name, "name", cfgName, "Output filename.")
	flag.StringVar(&name, "n", cfgName, "Output filename.")

	flag.BoolVar(&quiet, "quiet", cfgQuiet, "Suppress most text output (still show errors).")
	flag.BoolVar(&quiet, "q", cfgQuiet, "Suppress most text output (still show errors).")

	flag.BoolVar(&silent, "silent", cfgSilent, "Suppress all text output (including errors).")
	flag.BoolVar(&silent, "s", cfgSilent, "Suppress all text output (including errors).")

	flag.IntVar(&torPort, "tor-port", cfgTorPort, "Port your Tor service is listening on.")
	flag.IntVar(&torPort, "p", cfgTorPort, "Port your Tor service is listening on.")

	flag.BoolVar(&verbose, "verbose", cfgVerbose, "Show diagnostic details.")
	flag.BoolVar(&verbose, "v", cfgVerbose, "Show diagnostic details.")

	// Custom usage message to avoid duplicate entries for long & short flags
	flag.Usage = func() {
		w := flag.CommandLine.Output()
		msg := `tor-dl - fast large file downloader over locally installed Tor
Copyright © 2025 Bryan Cuneo <https://github.com/BryanCuneo/tor-dl/>
Licensed under GNU GPL version 3 <https://www.gnu.org/licenses/>
Based on torget by Michał Trojnara <https://github.com/mtrojnar/torget>

Usage: tor-dl [FLAGS] {file.txt | URL [URL2...]}
  -allow-http bool
        Allow tor-dl to download files over HTTP instead of HTTPS. Not recommended!
  -circuits, -c int
        Concurrent circuits. (default 20)
  -destination, -d string
        Output directory. (default current directory)
  -force bool
        Will create parent folder(s) and/or overwrite existing files.
  -min-lifetime, -l int
        Minimum circuit lifetime (seconds). (default 10)
  -name, -n string
        Output filename. (default filename from URL)
  -quiet, -q bool
        Suppress most text output (still show errors).
  -silent, -s bool
        Suppress all text output (including errors).
  -tor-port, -p int
        Port your Tor service is listening on. (default 9050)
  -verbose, -v
        Show diagnostic details.`

		fmt.Fprintln(w, msg)
	}
}

func main() {
	flag.Parse()

	// Если в localDebug.URL задан URL — используем его напрямую, CLI-аргумент не нужен.
	// Если localDebug.URL пустой — ждём URL из командной строки.
	if cfgURL == "" && flag.NArg() < 1 {
		flag.Usage()
		os.Exit(0)
	}

	// If the -quiet or -silent argument was used, don't print non-error text
	if quiet || silent {
		messageWriter = io.Discard

		// if -silent argument was used, also don't print errors
		if silent {
			errorWriter = io.Discard
		} else {
			errorWriter = os.Stderr
		}
	} else {
		messageWriter = os.Stdout
		errorWriter = os.Stderr
	}

	var uris []string

	// Приоритет: cfgURL > CLI-аргументы
	if cfgURL != "" {
		fmt.Fprintln(messageWriter, "[localDebug] Используется URL из кода:", cfgURL)
		uris = append(uris, cfgURL)
	} else if flag.NArg() == 1 {
		// Only one non-flag argument. Check if it's a URL or a text file
		if _, err := os.Stat(flag.Arg(0)); err == nil {
			// Found a file on disk, read URLs from it
			file, err := os.Open(flag.Arg(0))
			if err != nil {
				fmt.Fprintf(errorWriter, "ERROR: argument \"%s\" is not a valid URL or file.\n%v\n", flag.Arg(0), err)
				os.Exit(1)
			}
			defer file.Close()

			scanner := bufio.NewScanner(file)
			for scanner.Scan() {
				line := scanner.Text()
				// Filter out blank lines
				if line != "" {
					uris = append(uris, line)
				}
			}
		} else {
			// No file found on disk, treating argument as URL
			uris = append(uris, flag.Arg(0))
		}
	} else {
		// Multiple URLs passed as non-flag arguments
		uris = flag.Args()
	}

	if len(uris) > 1 {
		fmt.Fprintf(messageWriter, "Downloading %d files.\n", len(uris))

		// Ignore the -name argument when multiple files are provided, just use the URL's filename
		if name != "" {
			fmt.Fprintln(messageWriter, "WARNING: The -name argument is not usable when multiple URLs are provided. Ignoring.")
			name = ""
		}
	} else if len(uris) < 1 {
		fmt.Fprintln(errorWriter, "ERROR: No URLs found.")
		os.Exit(1)
	}

	bkgr := context.Background()

	// Iterate over each URL passed as an argument and download the file
	for i, uri := range uris {
		u, err := url.ParseRequestURI(uri)
		if err != nil {
			fmt.Fprintf(errorWriter, "ERROR: \"%s\" is not a valid URL.\n", uri)
			continue
		}

		if len(uris) > 1 {
			fmt.Fprintf(messageWriter, "\n[%d/%d] - %s\n", i+1, len(uris), uri)
		}

		if !allowHttp && u.Scheme != "https" {
			fmt.Fprintf(errorWriter, "ERROR: \"%s\" is not using HTTPS.\n\tIf you absolutely must use HTTP, use the -allow-http flag. This is dangerous and not recommended!\n", uri)
			continue
		}

		ctx := context.WithoutCancel(bkgr)
		state := NewState(ctx)
		state.Fetch(uri)
	}
}
