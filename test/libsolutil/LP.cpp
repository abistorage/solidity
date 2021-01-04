/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
// SPDX-License-Identifier: GPL-3.0

#include <libsolutil/LP.h>
#include <libsolutil/RationalVectors.h>
#include <libsmtutil/Sorts.h>
#include <libsolutil/StringUtils.h>
#include <test/Common.h>

#include <boost/test/unit_test.hpp>

using namespace std;
using namespace solidity::smtutil;
using namespace solidity::util;


namespace solidity::util::test
{

class LPTestFramework
{
public:
	LPTestFramework()
	{
		m_solvingState.variableNames.emplace_back("");
	}

	vector<rational> constant(rational _value)
	{
		return std::vector<rational>{_value};
	}

	vector<rational> variable(string const& _name)
	{
		if (m_solvingState.variableNames.empty())
			m_solvingState.variableNames.emplace_back("");
		auto index = findOffset(m_solvingState.variableNames, _name);
		if (!index)
		{
			index = m_solvingState.variableNames.size();
			m_solvingState.variableNames.emplace_back(_name);
		}
		return factorForVariable(*index, 1);
	}

	/// Adds the constraint "_lhs <= _rhs".
	void addLEConstraint(vector<rational> _lhs, vector<rational> _rhs)
	{
		_lhs = _lhs - _rhs;
		_lhs[0] = -_lhs[0];
		m_solvingState.constraints.push_back({move(_lhs), false});
	}

	void addLEConstraint(vector<rational> _lhs, rational _rhs)
	{
		addLEConstraint(move(_lhs), constant(_rhs));
	}

	/// Adds the constraint "_lhs = _rhs".
	void addEQConstraint(vector<rational> _lhs, vector<rational> _rhs)
	{
		_lhs = _lhs - _rhs;
		_lhs[0] = -_lhs[0];
		m_solvingState.constraints.push_back({move(_lhs), true});
	}

	void feasible(vector<pair<string, rational>> const& _solution)
	{
		auto [result, model] = m_solver.check(m_solvingState);
		BOOST_REQUIRE(result == LPResult::Feasible);
		for (auto const& [var, value]: _solution)
			BOOST_CHECK_MESSAGE(
				value == model.at(var),
				var + " = "s + toString(model.at(var)) + " (expected " + toString(value) + ")"
			);
	}

	void infeasible()
	{
		auto [result, model] = m_solver.check(m_solvingState);
		BOOST_CHECK(result == LPResult::Infeasible);
	}

protected:
	LPSolver m_solver;
	SolvingState m_solvingState;
};


BOOST_FIXTURE_TEST_SUITE(LP, LPTestFramework, *boost::unit_test::label("nooptions"))

BOOST_AUTO_TEST_CASE(basic)
{
	auto x = variable("x");
	addLEConstraint(2 * x, 10);
	feasible({{"x", 5}});
}

BOOST_AUTO_TEST_CASE(not_linear_independent)
{
	addLEConstraint(2 * variable("x"), 10);
	addLEConstraint(4 * variable("x"), 20);
	feasible({{"x", 5}});
}

BOOST_AUTO_TEST_CASE(two_vars)
{
	addLEConstraint(variable("y"), 3);
	addLEConstraint(variable("x"), 10);
	addLEConstraint(add(variable("x"), variable("y")), 4);
	feasible({{"x", 1}, {"y", 3}});
}

BOOST_AUTO_TEST_CASE(one_le_the_other)
{
	addLEConstraint(add(variable("x"), constant(2)), variable("y") - constant(1));
	feasible({{"x", 0}, {"y", 3}});
}

BOOST_AUTO_TEST_CASE(factors)
{
	auto x = variable("x");
	auto y = variable("y");
	addLEConstraint(2 * y, 3);
	addLEConstraint(16 * x, 10);
	addLEConstraint(add(x, y), 4);
	feasible({{"x", rational(5) / 8}, {"y", rational(3) / 2}});
}

// TODO test bounds!

#if 0
BOOST_AUTO_TEST_CASE(lower_bound)
{
	Expression x = variable("x");
	Expression y = variable("y");
	addLTConstraint(y >= 1);
	addLTConstraint(x <= 10);
	addLTConstraint(2 * x + y <= 2);
	feasible({{x, "0"}, {y, "2"}});
}

BOOST_AUTO_TEST_CASE(check_infeasible)
{
	Expression x = variable("x");
	addLTConstraint(x <= 3 && x >= 5);
	infeasible();
}

BOOST_AUTO_TEST_CASE(unbounded)
{
	Expression x = variable("x");
	addLTConstraint(x >= 2);
	// TODO the smt checker does not expose a status code of "unbounded"
	feasible({{x, "2"}});
}

BOOST_AUTO_TEST_CASE(unbounded_two)
{
	Expression x = variable("x");
	Expression y = variable("y");
	addLTConstraint(x + y >= 2);
	addLTConstraint(x <= 10);
	feasible({{x, "10"}, {y, "0"}});
}

BOOST_AUTO_TEST_CASE(equal)
{
	Expression x = variable("x");
	Expression y = variable("y");
	solver.addAssertion(x == y + 10);
	solver.addAssertion(x <= 20);
	feasible({{x, "20"}, {y, "10"}});
}

BOOST_AUTO_TEST_CASE(push_pop)
{
	Expression x = variable("x");
	Expression y = variable("y");
	solver.addAssertion(x + y <= 20);
	feasible({{x, "20"}, {y, "0"}});

	solver.push();
	solver.addAssertion(x <= 5);
	solver.addAssertion(y <= 5);
	feasible({{x, "5"}, {y, "5"}});

	solver.push();
	solver.addAssertion(x >= 7);
	infeasible();
	solver.pop();

	feasible({{x, "5"}, {y, "5"}});
	solver.pop();

	feasible({{x, "20"}, {y, "0"}});
}

BOOST_AUTO_TEST_CASE(less_than)
{
	Expression x = variable("x");
	Expression y = variable("y");
	solver.addAssertion(x == y + 1);
	solver.push();
	solver.addAssertion(y < x);
	feasible({{x, "1"}, {y, "0"}});
	solver.pop();
	solver.push();
	solver.addAssertion(y > x);
	infeasible();
	solver.pop();
}

BOOST_AUTO_TEST_CASE(equal_constant)
{
	Expression x = variable("x");
	Expression y = variable("y");
	solver.addAssertion(x < y);
	solver.addAssertion(y == 5);
	feasible({{x, "4"}, {y, "5"}});
}

BOOST_AUTO_TEST_CASE(chained_less_than)
{
	Expression x = variable("x");
	Expression y = variable("y");
	Expression z = variable("z");
	solver.addAssertion(x < y && y < z);

	solver.push();
	solver.addAssertion(z == 0);
	infeasible();
	solver.pop();

	solver.push();
	solver.addAssertion(z == 1);
	infeasible();
	solver.pop();

	solver.push();
	solver.addAssertion(z == 2);
	feasible({{x, "0"}, {y, "1"}, {z, "2"}});
	solver.pop();
}

BOOST_AUTO_TEST_CASE(splittable)
{
	Expression x = variable("x");
	Expression y = variable("y");
	Expression z = variable("z");
	Expression w = variable("w");
	solver.addAssertion(x < y);
	solver.addAssertion(x < y - 2);
	solver.addAssertion(z + w == 28);

	solver.push();
	solver.addAssertion(z >= 30);
	infeasible();
	solver.pop();

	solver.addAssertion(z >= 2);
	feasible({{x, "0"}, {y, "3"}, {z, "2"}, {w, "26"}});
	solver.push();
	solver.addAssertion(z >= 4);
	feasible({{x, "0"}, {y, "3"}, {z, "4"}, {w, "24"}});

	solver.push();
	solver.addAssertion(z < 4);
	infeasible();
	solver.pop();

	// z >= 4 is still active
	solver.addAssertion(z >= 3);
	feasible({{x, "0"}, {y, "3"}, {z, "4"}, {w, "24"}});
}

//#if 0

// TODO Move them to the tests for the boolean solver

BOOST_AUTO_TEST_CASE(boolean)
{
	Expression x = variable("x");
	Expression y = variable("y");
	Expression z = variable("z");
	solver.addAssertion(x <= 5);
	solver.addAssertion(y <= 2);
	solver.push();
	solver.addAssertion(x < y && x > y);
	infeasible();
	solver.pop();
	Expression w = booleanVariable("w");
	solver.addAssertion(w == (x < y));
	solver.addAssertion(w || x > y);
	feasible({{x, "0"}, {y, "3"}, {z, "2"}, {w, "26"}});
}

BOOST_AUTO_TEST_CASE(boolean_complex)
{
	Expression x = variable("x");
	Expression y = variable("y");
	Expression a = booleanVariable("a");
	Expression b = booleanVariable("b");
	solver.addAssertion(x <= 5);
	solver.addAssertion(y <= 2);
	solver.addAssertion(a == (x >= 2));
	solver.addAssertion(a || b);
	solver.addAssertion(b == !a);
	solver.addAssertion(b == (x < 2));
	feasible({{a, "1"}, {b, "0"}, {x, "5"}, {y, "2"}});
	solver.addAssertion(a && b);
	infeasible();
}

BOOST_AUTO_TEST_CASE(magic_square)
{
	vector<Expression> vars;
	for (size_t i = 0; i < 9; i++)
		vars.push_back(variable(string{static_cast<char>('a' + i)}));
	for (Expression const& var: vars)
		solver.addAssertion(1 <= var && var <= 9);
	// If we assert all to be mutually distinct, the problems gets too large.
	for (size_t i = 0; i < 9; i++)
		for (size_t j = i + 7; j < 9; j++)
			solver.addAssertion(vars[i] != vars[j]);
	for (size_t i = 0; i < 4; i++)
		solver.addAssertion(vars[i] != vars[i + 1]);
	for (size_t i = 0; i < 3; i++)
		solver.addAssertion(vars[i] + vars[i + 3] + vars[i + 6] == 15);
	for (size_t i = 0; i < 9; i += 3)
		solver.addAssertion(vars[i] + vars[i + 1] + vars[i + 2] == 15);
	feasible({
		{vars[0], "1"}, {vars[1], "0"}, {vars[2], "5"},
		{vars[3], "1"}, {vars[4], "0"}, {vars[5], "5"},
		{vars[6], "1"}, {vars[7], "0"}, {vars[8], "5"}
	});
}

BOOST_AUTO_TEST_CASE(boolean_complex_2)
{
	Expression x = variable("x");
	Expression y = variable("y");
	Expression a = booleanVariable("a");
	Expression b = booleanVariable("b");
	solver.addAssertion(x != 20);
	feasible({{x, "19"}});
	solver.addAssertion(x <= 5 || (x > 7 && x != 8));
	solver.addAssertion(a = (x == 9));
	feasible({{a, "1"}, {b, "0"}, {x, "5"}});
//	solver.addAssertion(!a || (x == 10));
//	solver.addAssertion(b == !a);
//	solver.addAssertion(b == (x < 200));
//	feasible({{a, "1"}, {b, "0"}, {x, "5"}});
//	solver.addAssertion(a && b);
//	infeasible();
}


BOOST_AUTO_TEST_CASE(pure_boolean)
{
	Expression a = booleanVariable("a");
	Expression b = booleanVariable("b");
	Expression c = booleanVariable("c");
	Expression d = booleanVariable("d");
	Expression e = booleanVariable("e");
	Expression f = booleanVariable("f");
	solver.addAssertion(a && !b);
	solver.addAssertion(b || c);
	solver.addAssertion(c == (d || c));
	solver.addAssertion(f == (b && !c));
	solver.addAssertion(!f || e);
	solver.addAssertion(c || d);
	feasible({});
	solver.addAssertion(a && b);
	infeasible();
}
#endif

BOOST_AUTO_TEST_SUITE_END()

}
