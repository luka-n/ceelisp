CC=gcc
CFLAGS=-std=c99 -Wpedantic -g -Wall -Wextra

ceelisp: ceelisp.c
	$(CC) $(CFLAGS) -o ceelisp ceelisp.c

clean:
	rm -f ceelisp
