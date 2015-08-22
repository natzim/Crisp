crisp: crisp.c mpc.c
	gcc -Wall crisp.c mpc.c -ledit -lm -o bin/crisp
