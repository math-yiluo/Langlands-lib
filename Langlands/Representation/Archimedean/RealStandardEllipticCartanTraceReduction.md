# Elliptic Cartan comparison from compact trace limits

`RealStandardEllipticCartanTraceLimitsStatement` asks for one Haar measure and one nontrivial
filter of continuous tests on the orthogonal group at each separated regular Cartan point.
The corresponding traces are `compactTestTrace` evaluated on the actual `cartanElement`.
Both formulas assume that the original list has the Cartan's total rank and is a permutation
of the indicated enumeration of induced blocks and real characters, with every enumerated
induced weight strictly positive. If the list has fewer induced blocks than the Cartan has
complex planes, the required limit is zero. At equal elliptic ranks the required limit is the
finite numerator times a nonzero scalar. The measure, filter and scalar are shared across
the original block lists and their enumerations.

The Lean proof chooses these data at each separated regular point and uses `Filter.limUnder`
for the scalar evaluation. For the original lists and their given bijective compact and Lie
intertwiner, `realStandardCompactTestTrace` gives equality as functions of the continuous test.
Consequently the chosen limits agree. The supplied convergence and the nontriviality of the
filter identify the chosen limit in each formula clause. The compact trace evaluation then
satisfies the hypothesis of `realStandardEllipticCartanComparison_of_evaluation`, which gives
the common counts and equality of the full finite numerators.

This is an internal reduction through the Library's continuous compact trace theorem. The
support and equal-rank convergence formulas for the compact traces are its analytic premise.
