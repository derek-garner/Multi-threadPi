// ------------------------------------------------------------------
//
// Adapted From: http://stackoverflow.com/questions/5905822/function-to-find-the-nth-digit-of-pi
// Other references:
//		http://bellard.org/pi/pi_n2/pi_n2.html
//		https://web.archive.org/web/20150627225748/http://en.literateprograms.org/Pi_with_the_BBP_formula_%28Python%29
//
// ------------------------------------------------------------------
/*
* Computation of the n'th decimal digit of \pi with very little memory.
* Written by Fabrice Bellard on January 8, 1997.
*
* We use a slightly modified version of the method described by Simon
* Plouffe in "On the Computation of the n'th decimal digit of various
* transcendental numbers" (November 1996). We have modified the algorithm
* to get a running time of O(n^2) instead of O(n^3log(n)^3).
*
* This program uses mostly integer arithmetic. It may be slow on some
* hardwares where integer multiplications and divisons must be done
* by software. We have supposed that 'int' has a size of 32 bits. If
* your compiler supports 'long long' integers of 64 bits, you may use
* the integer version of 'mul_mod' (see HAS_LONG_LONG).
*/

#include <iostream>
#include <sstream>
#include <cstdlib>
#include <cmath>
#include <string>
#include <queue>
#include <mutex>
#include <thread>
#include <unordered_map>

/* uncomment the following line to use 'long long' integers */
/* #define HAS_LONG_LONG */

//#ifdef HAS_LONG_LONG
#define mul_mod(a,b,m) (( (long long) (a) * (long long) (b) ) % (m))
//#else
//	#define mul_mod(a,b,m) std::fmod( (double) a * (double) b, m)
//#endif

/* return the inverse of x mod y */
int inv_mod(int x, int y)
{
	int q, u, v, a, c, t;

	u = x;
	v = y;
	c = 1;
	a = 0;
	do {
		q = v / u;

		t = c;
		c = a - q * c;
		a = t;

		t = u;
		u = v - q * u;
		v = t;
	} while (u != 0);
	a = a % y;
	if (a < 0)
		a = y + a;
	return a;
}

/* return (a^b) mod m */
int pow_mod(int a, int b, int m)
{
	int r, aa;

	r = 1;
	aa = a;
	while (1) {
		if (b & 1)
			r = mul_mod(r, aa, m);
		b = b >> 1;
		if (b == 0)
			break;
		aa = mul_mod(aa, aa, m);
	}
	return r;
}

/* return true if n is prime */
int is_prime(int n)
{
	int r, i;
	if ((n % 2) == 0)
		return 0;

	r = (int)(sqrt(n));
	for (i = 3; i <= r; i += 2)
		if ((n % i) == 0)
			return 0;
	return 1;
}

/* return the prime number immediatly after n */
int next_prime(int n)
{
	do {
		n++;
	} while (!is_prime(n));
	return n;
}

unsigned int computePiDigit(int n)
{
	int av, a, vmax, N, num, den, k, kq, kq2, t, v, s, i;
	double sum = 0;

	N = (int)((n + 20) * std::log(10) / std::log(2));

	for (a = 3; a <= (2 * N); a = next_prime(a)) {

		vmax = (int)(std::log(2 * N) / std::log(a));
		av = 1;
		for (i = 0; i < vmax; i++)
			av = av * a;

		s = 0;
		num = 1;
		den = 1;
		v = 0;
		kq = 1;
		kq2 = 1;

		for (k = 1; k <= N; k++) {

			t = k;
			if (kq >= a) {
				do {
					t = t / a;
					v--;
				} while ((t % a) == 0);
				kq = 0;
			}
			kq++;
			num = mul_mod(num, t, av);

			t = (2 * k - 1);
			if (kq2 >= a) {
				if (kq2 == a) {
					do {
						t = t / a;
						v++;
					} while ((t % a) == 0);
				}
				kq2 -= a;
			}
			den = mul_mod(den, t, av);
			kq2 += 2;

			if (v > 0) {
				t = inv_mod(den, av);
				t = mul_mod(t, num, av);
				t = mul_mod(t, k, av);
				for (i = v; i < vmax; i++)
					t = mul_mod(t, a, av);
				s += t;
				if (s >= av)
					s -= av;
			}

		}

		t = pow_mod(10, n - 1, av);
		s = mul_mod(s, t, av);
		sum = std::fmod(sum + (double)s / (double)av, 1.0);
	}

	return static_cast<unsigned int>(sum * 1e9 / 100000000);
}

// ------------------------------------------------------------------
//
// Code adapted from this source: https://web.archive.org/web/20150627225748/http://en.literateprograms.org/Pi_with_the_BBP_formula_%28Python%29
//
// ------------------------------------------------------------------
double powneg(unsigned long long b, long long pow)
{
	double r = std::pow(b, -pow);
	return 1.0 / r;
}

unsigned long long s(unsigned long long j, unsigned long long n)
{
	const unsigned long long D = 14;
	const unsigned long long M = static_cast<unsigned long long>(std::pow(16, D));
	const unsigned long long SHIFT = 4 * D;
	const unsigned long long MASK = M - 1;

	unsigned long long s = 0;
	unsigned long long k = 0;
	while (k <= n)
	{
		unsigned long long r = 8 * k + j;
		unsigned long long v = static_cast<unsigned long long>(std::pow(16ul, n - k)) % r;
		s = (s + (v << SHIFT) / r) & MASK;
		k += 1;
	}
	unsigned long long t = 0;
	k = n + 1;
	while (true)
	{
		unsigned long long xp = static_cast<unsigned long long>(powneg(16, n - k) * M);
		unsigned long long newt = t + xp / (8 * k + j);
		if (t == newt)
			break;
		else
			t = newt;
		k += 1;
	}

	return s + t;
}

unsigned long long piDigitHex(unsigned long long n)
{
	const unsigned long long D = 14;
	const unsigned long long M = static_cast<unsigned long long>(std::pow(16, D));
	const unsigned long long SHIFT = 4 * D;
	const unsigned long long MASK = M - 1;

	n -= 1;
	unsigned long long x = (4 * s(1, n) - 2 * s(4, n) - s(5, n) - s(6, n)) & MASK;

	return x;
}



struct Task {
	int id;
	unsigned int computePi() {
		return computePiDigit(id);
	}
};

struct piDigitEntry {
	int id;
	int value;
	
};



//Task queue for threads
class TaskList {
public:
	void push(Task task) {
		piQueue.push(task);
	}
	void lock() {
		queueMutex.lock();
	}
	void unlock() {
		queueMutex.unlock();
	}
	bool isEmpty() {
		return piQueue.empty();
	}

	int getPieDigit() {
		piQueue.front().id;
	}
	Task getTask() {
		return piQueue.front();
	}
	void pop() {
		piQueue.pop();
	}
private:
	std::queue<Task> piQueue;	
	std::mutex queueMutex;
};

//Hash table to store result
class PieTable {
public:
	void lock() {
		hashMutex.lock();
	}
	void unlock() {
		hashMutex.unlock();
	}
	void insertValue(int key,unsigned int value) {
		pieMap.insert({ key, value });
	}
	int get(int index) {
		return pieMap[index];
	}
private:
	std::mutex hashMutex;
	std::unordered_map<int,unsigned int> pieMap;

};



int main()
{
	
	int numDigitsPie=1000;
	TaskList taskList;
	PieTable pieTable;
	std::unordered_map<int, unsigned int> pieMap;
	int numThreads = std::thread::hardware_concurrency();
	std::cout << "Computing pi with " << numThreads << " threads \n";
	std::cout << numDigitsPie << " Digits\n";

	//Begin by loading the queue with digits of pie
	
	//Load index for pie digits into queue
	for (int i = 1; i < numDigitsPie;i++) {
		Task temp{ i };
		taskList.push(temp);
	}

	auto threadFunction =
		[&taskList, &pieTable, numDigitsPie,&pieMap](uint16_t which)
	{
		while (!taskList.isEmpty()){
			std::cout.flush();
			std::cout << ".";
			taskList.lock();
			Task taskTemp = taskList.getTask();
			taskList.pop();
			taskList.unlock();
			int pieIndex = taskTemp.id;
			int pieNumber = taskTemp.computePi();
			pieTable.lock();
			pieTable.insertValue(pieIndex, pieNumber);
			pieTable.unlock();
		}
	};
	
	//Test for queue being empty
	
	//Dynamically create thread array
	std::thread *threads;
	threads = new std::thread[numThreads];

	//Run threads then join
	for (int i = 0; i < numThreads; i++) {threads[i]= std::thread(threadFunction, i);}
	for (int i = 0; i < numThreads; i++) {threads[i].join();}

	//Print results :)
	std::cout.flush();
	std::cout << "\n3.";
	for (int i = 1; i < numDigitsPie; i++) {
		std::cout << pieTable.get(i);
	}
	std::cout << std::endl;


	return 0;
}


/*


Create a FIFO queue that stores the compute tasks (http://www.cplusplus.com/reference/queue/queue/ (Links to an external site.)Links to an external site.).
This queue must be protected against race conditions.
At program startup, before creating any of the worker threads, fully populate this queue with 1 task per digit to be computed; 1000 tasks.  Each task will say which digit to compute.
This is a shared resource available to all worker threads (not a global variable, however).
Use aggregation, rather than inheritance, to create this queue.  Use a mutex, private to the queue, to protect the write/read operations.


Create a hash table to store the results (http://www.cplusplus.com/reference/unordered_map/unordered_map/ (Links to an external site.)Links to an external site.).  Each entry in the hash table has as its key the digit position and the computed Pi digit as its value.
This hash table must be protected against race conditions.
This is a shared resource available to all worker threads (not a global variable, however).
Use aggregation, rather than inheritance, to create this hash table.  Use a mutex, private to the hash table, to protect the write/read operations.


Create as many worker threads as there are CPU cores (std::thread::hardware_concurrency()); rather than hard-coding the number of threads.  Each of these worker threads obtains a task from the FIFO task queue, computes the requested digit, then stores the result in the hash table.  It continues retrieving tasks from the queue until there are none, then it voluntarily terminates.
As each worker begins a task, print a "." to the screen to indicate progress.  You may/will need to execute a std::cout.flush() right after printing the "." to ensure it gets displayed to the console immediately.
When the FIFO queue is empty and all threads have finished their work, display the computed value of Pi.
After the display is complete, the program should gracefully exit.
I've provided a screenshot of a sample run on my program at the end of this page; have your output match this approach.  On my Raspberry Pi it took almost 3 minutes (2 minutes, 51 seconds) to run.  The same run takes 8.8 seconds on my desktop system (8 CPU cores).



















*/