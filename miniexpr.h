#ifndef __MINIEXPR_H__
#define __MINIEXPR_H__

#include <string>

namespace me {
// namespace miniexpr
struct expr {
	int type;
	union {
		double value;
		const double *bound;
		const void *function;
	};
	void *parameters [1];
};

enum {
	VARIABLE = 0,

	FUNCTION0 = 8, FUNCTION1, FUNCTION2, FUNCTION3,
	FUNCTION4, FUNCTION5, FUNCTION6, FUNCTION7,

	CLOSURE0 = 8, CLOSURE1, CLOSURE2, CLOSURE3,
	CLOSURE4, CLOSURE5, CLOSURE6, CLOSURE7,

	FLAG_PURE = 32
};

struct variable {
	std::string_view name;
	const void *address;
	int type;
	void *context;
};
// 立即执行表达式，错误则设置error为0，返回 NaN
double interp (std::string_view expression, int *error);
// 延迟执行，绑定变量
expr *compile (std::string_view expression, const variable variables, int var_count, int *error);
// 计算表达式
double eval (const expr *n);
// 输出调试信息通过一个 synyax tree
void print (const expr *n);
void free (const expr *n);

};

#endif