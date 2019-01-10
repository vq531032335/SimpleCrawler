import socket
from math import log
from time import time
from urllib import request, robotparser
from urllib.error import HTTPError, URLError
from urllib.parse import urlparse, urljoin
from queue import Queue, PriorityQueue
from html.parser import HTMLParser
import os
import mimetypes


class MyHTMLParser(HTMLParser):
    """
    a class inherited from HTMLParser, most functions are overloaded

    not using beautiful soup
    """
    def __init__(self):
        HTMLParser.__init__(self)
        self.links = {}
        self.text = ""
        self.is_text = False

    def handle_starttag(self, tag, attrs):
        # get all the href's value
        if tag == "a":
            self.is_text = True
            if len(attrs) > 0:
                for (variable, value) in attrs:
                    if variable == "href":
                        if value is not None and len(value) > 0:
                            self.links[value] = 0

    def handle_endtag(self, tag):
        if tag == 'a':
            self.is_text = False

    def handle_data(self, data):
        # get all the data
        if self.is_text:
            self.text += ' ' + data.lower()

    def error(self, message):
        pass


class Website:
    """
    a class storing one website's information and managing limiting pages per site

    """
    def __init__(self, url):
        self.web_url = url
        self.pages_limit = 10  # this number can be changed, -1 means infinite

        # Robot Exclusion Protocol
        self.has_robot = False
        self.robot_parser = robotparser.RobotFileParser()
        robot_url = "http://" + url + "/robots.txt"
        self.robot_parser.set_url(robot_url)
        self.robot_create()

    def robot_create(self):
        if not self.has_robot:
            try:
                self.robot_parser.read()
                self.has_robot = True
                # print("robot read succeed: " + robot_url)
            except HTTPError as re:
                # print("robot read fail:" + re.reason + ": " + robot_url)
                pass
            except URLError as re:
                # print("robot read fail:" + re.reason + ": " + robot_url)
                pass
            except socket.timeout:
                # print("robot read timeout: " + robot_url)
                pass
            except UnicodeDecodeError:
                # print("robot read fail:UnicodeDecodeError" + robot_url)
                pass
            except ConnectionResetError:
                pass
            except Exception:
                pass

    def compare(self, url):  # True if equal
        return url == self.web_url

    def page_full(self):  # True if beyond limit pages per site
        return self.pages_limit == 0

    def add_page(self):
        self.pages_limit -= 1

    def robot_access(self, user_agent, url):  # determine whether accessible by the website
        if self.has_robot:
            return self.robot_parser.can_fetch(user_agent, url)
        else:
            return True


class Url:
    """
    a class combined with url and its priority
    """
    def __init__(self, url, father_url="", priority=0.0):
        self.url = url
        self.father_url = father_url
        self.referenced_number = 0
        self.priority = priority
        return

    def __lt__(self, other):  # function of '<', use > because priority queue output min first
        return self.priority > other.priority

    def add_priority(self, value, times=1):
        pri_sum = self.priority * self.referenced_number
        pri_sum += value
        self.referenced_number += times
        self.priority = pri_sum / self.referenced_number


class PageResult:
    """
    a class storing the information of a visited page's output
    """
    def __init__(self, url, size, address, depth, score):
        self.page_url = url
        self.page_size = size
        self.page_dir = address
        self.page_depth = depth
        self.page_estimated_score = score
        self.text_length = None
        self.term_frequency = None
        self.relevance = 0.0

    def info(self, is_rel):
        information = ""
        information += self.page_url
        information += " pageSize: " + str(round(self.page_size/1024, 2)) + "KB"
        information += " fileAddress: " + self.page_dir
        information += " pageDepth: " + str(self.page_depth)
        information += " estimatedPriority: " + str(round(self.page_estimated_score, 2))
        if is_rel:
            information += " relevanceScore: " + str(round(self.relevance, 2))
        return information

    def put_statistics(self, statistics):
        self.text_length = statistics[0]
        self.term_frequency = statistics[1:]

    def set_relevance(self, rel):
        self.relevance = rel


class Crawler:
    """
    major class of the program

    """
    def __init__(self, content, num, setting):
        self.headers = [('User-agent', 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) '
                                  'Chrome/64.0.3282.167 Safari/537.36')]
        self.page_dir = 'Pages'

        self.search_target = content.lower().split(' ')
        self.max_pages = num

        self.met_urls = {}  # diction of met urls
        self.candidate_urls_google = Queue()
        if setting == 1:  # focused crawling
            self.candidate_urls = PriorityQueue()
        else:  # BFS crawling
            self.candidate_urls = Queue()
        self.candidate_extra_priority = {}  # diction of extra_priority
        self.candidate_extra_number = {}  # diction of extra_number

        self.visited_websites = {}  # diction of Website
        self.visited_urls = {}  # diction of PageResult

        self.error_count = 0
        return

    def start(self):
        """
        first get the initial urls from google, get new urls by loop, create a result.txt in the end

        :return:
        """
        # get the search url
        google_url = "https://www.google.com/search?q="
        search_addition = '+'.join(self.search_target)
        result = self.get_page(google_url + search_addition)

        if result[0] == "success":
            # remove old files
            for file in os.listdir(self.page_dir):
                path_file = os.path.join(self.page_dir, file)
                if os.path.isfile(path_file):
                    os.remove(path_file)

            # get urls from google search
            self.read_google_page(result[1])
            # read these pages
            self.pre_process()
            self.compute_bm25()
            self.refresh_priority()

            # main process
            start_time = time()
            self.main_process()
            end_time = time()
            total_time = end_time - start_time

            # compute the relevance of each page and output the result file
            harvest_rate = self.compute_bm25()

            final_result = [""]
            total_size = 0
            for url_key in self.visited_urls:
                total_size += self.visited_urls[url_key].page_size
                final_result.append(self.visited_urls[url_key].info(True))

            statistic_result = "number of files:" + str(self.max_pages) + "  total size:" + str(round(total_size/1024, 2)) + "KB  total time:" +\
                               str(round(total_time, 2)) + "s  number of 404/403 errors: " + str(self.error_count) + "  harvest rate:" + str(round(harvest_rate, 2))
            final_result[0] = statistic_result
            save_page("result.txt", final_result)
            print("Job done. " + statistic_result)
        else:
            print("google search not allowed, please try again")

    def pre_process(self):
        """
        visit all the google urls

        :return:
        """
        while len(self.visited_urls) != self.max_pages and not self.candidate_urls_google.empty():
            # get a url[url, priority] from candidate urls
            now_url = self.candidate_urls_google.get()
            self.visit_url(now_url)

    def main_process(self):
        """
        do the loop

        :return:
        """
        while len(self.visited_urls) != self.max_pages and not self.candidate_urls.empty():
            # get a url[url, priority] from candidate urls
            now_url = self.candidate_urls.get()
            self.visit_url(now_url)

    def visit_url(self, visit_url):
        now_url_parse = urlparse(visit_url.url)
        now_url_depth = now_url_parse[2].count('/')
        now_website_url = now_url_parse[1]
        if now_website_url.count("wikipedia") > 0:
            now_website_url = "wikipedia.org"
        # get the website from url
        now_website = self.get_website(now_website_url)
        if not now_website.page_full() and now_url_depth < 10:  # should not beyond pages per site and max depth
            if now_website.robot_access('*', visit_url.url):  # determine whether the url is accessible by robot
                now_website.add_page()  # maintain pages per site
                # start visit this page
                page_now = self.get_page(visit_url.url)
                if page_now[0] == "success":  # visit success
                    page_content = page_now[1]
                    page_dir = page_now[2]
                    # insert url info into visited dictionary
                    now_page_result = PageResult(visit_url.url, len(page_content), page_dir, now_url_depth,
                                                 visit_url.priority)
                    self.visited_urls[visit_url.url] = now_page_result
                    # get more candidate urls by this page
                    self.read_page(page_content, visit_url.url, now_page_result)
                    print("page visit success: " + now_page_result.info(False))
                else:
                    if page_now[0] == 404 or page_now[0] == 403:
                        self.error_count += 1
                    print("page visit failure(" + str(page_now[0]) + "): " + visit_url.url)
                    pass
            else:
                print("not allowed by robot: " + visit_url.url)
        else:
            print("beyond limit per site: " + visit_url.url)

    def get_website(self, web_url):
        """
        try to find whether the website is met before, if not, create a new one

        :param web_url:
        :return: object of the website
        """
        for web_key in self.visited_websites:
            if self.visited_websites[web_key].compare(web_url):  # the website we are looking for exists
                return self.visited_websites[web_key]
        else:
            # create a new website class
            new_website = Website(web_url)
            self.visited_websites[web_url] = new_website
            return new_website

    def get_page(self, page_url):
        import socket
        """
        get html content from a url

        :param page_url: url address
        :return: page_result = list[result, page_text, page_file]
        """
        page_result = []
        try:
            opener = request.build_opener()
            opener.addheaders = self.headers
            request.install_opener(opener)
            file_dir = self.page_dir + '/page' + str(len(self.visited_urls)) + '.txt'
            socket.setdefaulttimeout(5)
            request.urlretrieve(page_url, file_dir, schedule)
            html = open(file_dir, errors='ignore')
            page = html.read()
            html.close()
            # page result[stat, page content, file direction]
            page_result.append("success")
            page_result.append(page)
            page_result.append(file_dir)
        except request.HTTPError as re:
            page_result.append(re.code)
        except request.URLError as re:
            page_result.append(re.reason)
        except socket.timeout:
            page_result.append("timeout")
        except UnicodeEncodeError:
            page_result.append("UnicodeEncodeError")
        except Exception:
            page_result.append("Error")
        return page_result

    def add_candidate(self, url, father_url, priority=0):
        if url not in self.met_urls:  # determine whether the url is met before
            self.met_urls[url] = 0
            self.candidate_urls.put(Url(url, father_url, priority))
        else:  # if a url is referenced again, add extra priority
            if url not in self.candidate_extra_priority:
                self.candidate_extra_priority[url] = priority
                self.candidate_extra_number[url] = 1
            else:
                self.candidate_extra_priority[url] += priority
                self.candidate_extra_number[url] += 1

    def read_google_page(self, page):
        """
        a special function to transform google result to urls and put them into candidate_urls(ignore robots)

        :param page: google search page
        :return:
        """
        import re
        # use regular expression to get search result from google
        pattern = re.compile('class="r".*?><a href="(.*?)".*?' +
                             '">(.*?)' +
                             '</a>', re.S)
        items = re.findall(pattern, page)
        a = 0
        for item in items:
            a += 1
            if a > 10:
                break
            print(str(a) + "st google search result: " + item[0])
            self.met_urls[item[0]] = 0
            self.candidate_urls_google.put(Url(item[0]))  # [0] means first item in pattern
        if self.candidate_urls_google.empty():
            print("google search not allowed, please try again")

    def read_page(self, page_html, page_url, page_result):
        """
        transform html to urls, compute page statistics, and put urls into candidate queue

        :param page_url: url text
        :param page_html: html text
        :param page_result: pageResult
        :return:
        """
        html_parser = MyHTMLParser()
        try:
            html_parser.feed(page_html)
        except Exception:
            pass

        page_statistics = [len(html_parser.text)]
        for item in self.search_target:
            word_count = html_parser.text.count(item)
            page_statistics.append(word_count)
        page_result.put_statistics(page_statistics)
        self.compute_bm25(page_url)

        # put useful urls into candidate urls
        for link in html_parser.links:
            new_url = urljoin(page_url, link)
            # unfortunately most urls have no file endings, need to consider None as an option
            if mimetypes.guess_type(link)[0] == "text/html" or mimetypes.guess_type(link)[0] is None:
                self.add_candidate(new_url, page_url, page_result.relevance)
        self.refresh_priority(True)

    def refresh_priority(self, is_extra=False):
        """
        refresh google results' child url priority(is_extra==False)
        refresh priority of urls which has been referenced again(is_extra==True)

        :return:
        """
        temp_q = Queue()
        while not self.candidate_urls.empty():
            temp_u = self.candidate_urls.get()

            for visited_url_key in self.visited_urls:
                if is_extra is False:
                    if temp_u.father_url == self.visited_urls[visited_url_key].page_url:
                        temp_u.add_priority(self.visited_urls[visited_url_key].relevance)
                else:
                    if temp_u.url in self.candidate_extra_priority:
                        temp_u.add_priority(self.candidate_extra_priority[temp_u.url], self.candidate_extra_number[temp_u.url])
            temp_q.put(temp_u)

        while not temp_q.empty():
            self.candidate_urls.put(temp_q.get())
        self.candidate_extra_priority.clear()
        self.candidate_extra_number.clear()
        pass

    def compute_bm25(self, target_url=None):
        """
        compute relevance based on visited pages and get final harvest rate

        :param target_url: text of target url    if None: refresh every url else: refresh only target
        :return:harvest rate
        """
        harvest_rate = 0.0
        urls = self.visited_urls
        target_num = len(self.search_target)
        if urls is None:
            return harvest_rate
        big_n = len(urls)  # total number of documents in the collection
        ft = []  # number of documents that contain term t
        for i in range(0, target_num):
            fre_sum = 0
            for url_key in urls:
                if urls[url_key].term_frequency[i] > 0:
                    fre_sum += 1
            ft.append(fre_sum)

        len_sum = 0
        for url_key in urls:
            len_sum += urls[url_key].text_length
        d_avg = len_sum / len(urls)  # the average length of documents in the collection
        k1 = 1.2
        b = 0.75

        harvest_sum = 0
        for url_key in urls:
            point = 0.0
            big_k = k1 * ((1 - b) + b * urls[url_key].text_length / d_avg)
            for i in range(0, target_num):
                fdt = urls[url_key].term_frequency[i]
                value = log((big_n + 0.5) / (ft[i] + 0.5)) * (
                            (k1 + 1) * fdt / (big_k + fdt))  # replace (N - ft[i]+ 0.5) with (N + 0.5)
                point += value
            if target_url is None or urls[url_key].page_url == target_url:
                urls[url_key].set_relevance(point)
            if point > 0.3:  # this value can be changed
                harvest_sum += 1

        harvest_rate = harvest_sum / len(urls)
        return harvest_rate


def save_page(filename, content):
    """
    save a list into a file

    :param filename: file address
    :param content: a list of file content
    :return:
    """
    import codecs
    file = codecs.open(filename, "w")
    for lines in content:
        file.writelines(lines + '\n')
    file.close()


def schedule(block_num, block_size, total_size):
    """
    progress showing function for urlretrieve(), just for debug

    :param block_num:
    :param block_size:
    :param total_size:
    :return:
    """
    # percent = 0.0
    # if total_size != 0:
    #    percent = 100.0 * block_num * block_size / total_size
    #    if percent > 100:
    #        percent = 100
    # print(percent + '%')
    pass


search_content = input("search:")
search_num = int(input("maximum pages (-1 means infinite search):"))
search_setting = int(input("enter 1 or 2 (1 means focused crawling, 2 means BFS crawling):"))
cc = Crawler(search_content, search_num, search_setting)
cc.start()
