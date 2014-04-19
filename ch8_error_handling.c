#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#include <editline/readline.h>
#include "mpc.h"


typedef struct {
	int type;
    union {
        long num;
        int err;
    } val;
} lval;

enum lval_type { LVAL_NUM, LVAL_ERR };

enum err_code { LERR_DIV_ZERO, LERR_BAD_OP, LERR_BAD_NUM };

lval lval_num(long x) {
	lval v;
	v.type = LVAL_NUM;
	v.val.num = x;
	return v;
}

lval lval_err(int x) {
	lval v;
	v.type = LVAL_ERR;
	v.val.err = x;
	return v;
}

void lval_print(lval v) {
	switch (v.type) {
		case LVAL_NUM: printf("%li", v.val.num); break;

		case LVAL_ERR:
			if (v.val.err == LERR_DIV_ZERO) { printf("Error: Division by zero!"); }
			if (v.val.err == LERR_BAD_OP) { printf("Error: Invalid operator!"); }
			if (v.val.err == LERR_BAD_NUM) { printf("Error: Invalid number!"); }
		break;
	}
}

void lval_println(lval v) {
	lval_print(v); putchar('\n');
}

lval eval_op(lval x, char* op, lval y) {
	if (x.type == LVAL_ERR) { return x; }
	if (y.type == LVAL_ERR) { return y; }

	if (strcmp(op, "+") == 0) { return lval_num(x.val.num + y.val.num); }
	if (strcmp(op, "-") == 0) { return lval_num(x.val.num - y.val.num); }
	if (strcmp(op, "*") == 0) { return lval_num(x.val.num * y.val.num); }
	if (strcmp(op, "/") == 0) { 
		if (y.val.num == 0) { return lval_err(LERR_DIV_ZERO); }; 
		return lval_num(x.val.num / y.val.num); 
	}
	if (strcmp(op, "%") == 0) { 
		if (y.val.num == 0) { return lval_err(LERR_DIV_ZERO); }; 
		return lval_num(x.val.num % y.val.num); 
	}
	if (strcmp(op, "^") == 0) { return lval_num(pow(x.val.num, y.val.num)); }
	if (strcmp(op, "min") == 0) { return lval_num(x.val.num < y.val.num ? x.val.num : y.val.num); }
	if (strcmp(op, "max") == 0) { return lval_num(x.val.num > y.val.num ? x.val.num : y.val.num); }

	return lval_err(LERR_BAD_OP);
}

lval eval(mpc_ast_t* t) {
	if (strstr(t->tag, "number")) {
		errno = 0;
		long x = strtol(t->contents, NULL, 10);
		if (errno == ERANGE) { return lval_err(LERR_BAD_NUM); }
		return lval_num(x);
	}

	char* op = t->children[1]->contents;
	lval x = eval(t->children[2]);

	int i = 3;
	while (strstr(t->children[i]->tag, "expr")) {
		x = eval_op(x, op, eval(t->children[i]));
		i++;
	}

	if (t->children_num == 4 && strcmp(op, "-") == 0 && x.type == LVAL_NUM) {
		x.val.num = -x.val.num;
	}

	return x;
}

int main(int argc, char** argv) {
	mpc_parser_t* Number = mpc_new("number");
	mpc_parser_t* Operator = mpc_new("operator");
	mpc_parser_t* Expr = mpc_new("expr");
	mpc_parser_t* Lispy = mpc_new("lispy");

	puts("Declared parsers");

	mpca_lang(MPC_LANG_DEFAULT,
		"                                                                      \
			number   : /-?[0-9]+/ ;                                            \
			operator : '+' | '-' | '*' | '/' | '%' | '^' | \"min\" | \"max\" ; \
			expr     : <number> | '(' <operator> <expr>+ ')' ;                 \
			lispy    : /^/ <operator> <expr>+ /$/ ;                            \
		",
		Number, Operator, Expr, Lispy);

	puts("Parsed parsers");

	puts("Krispy version 0.0.0.0.1");
	puts("Press Ctrl+C to Exit\n");

	while (1) {
		char* input = readline("krispy> ");
		add_history(input);

		mpc_result_t r;
		if (mpc_parse("<stdin>", input, Lispy, &r)) {
			lval result = eval(r.output);
			lval_println(result);
			mpc_ast_delete(r.output);
		} else {
			mpc_err_print(r.error);
			mpc_err_delete(r.error);
		}

		free(input);
	}

	mpc_cleanup(4, Number, Operator, Expr, Lispy);

	return 0;
}
