# Orbit weights under a reversing cocharacter point

This is an internal algebraic consequence of the published diagonal-cocharacter
matrix description and the actual matrix representation API.

Let k be an arbitrary field, G a group scheme over k, and rho an actual finite
matrix representation of G. The matrix-entry and orbit-bound theorems assume
that chi acts diagonally in the chosen coordinates with integer weights e:
`chi ≫ rho = GeneralLinear.diagonalCocharacter ... e`.

`ReversesCocharacter chi s` states that conjugation by the actual rational point
s carries chi to its inverse. `HasOrbitWeightLowerBound rho e j` means that the
orbit of the j-th coordinate vector, on every scheme test, has zero coordinate
a whenever e(a) is strictly less than -e(j).

A reversing point acts by a rational matrix whose (a,b) entry vanishes unless
e(a)=-e(b). To prove this, evaluate the conjugation identity at the universal
Laurent unit. Comparing its matrix entries gives a constant Laurent monomial
with exponent e(a)+e(b). Distinct Laurent monomials have distinct coefficients,
so its coefficient vanishes when that exponent is nonzero. The inverse point
also reverses the cocharacter.

The lower-bound and nonnegativity theorems additionally assume
`rho.HasOrbitWeightUpperBound e j`: on every relative scheme test, every
coordinate b of every orbit column is zero whenever e(j)<e(b). Cocharacter
reversal alone does not supply this hypothesis. Under this upper-bound
assumption and an actual reversing rational point, the lower-bound theorem
proceeds as follows.

For an arbitrary test and orbit column, write its matrix as the product of the
matrix of the inverse reversing point and the matrix of the translated orbit
point. In each entry strictly below -e(j), each summand vanishes: either its
translated-orbit coordinate is above e(j) and vanishes by the assumed all-test
upper bound, or the reversing-point matrix entry has unequal opposite weights.
Pulling the rational matrix entries to the test scheme gives the conclusion
without a reducedness assumption on that test.

The identity orbit vector has a nonzero j-th coordinate. Applying the lower
bound to it proves e(j) is nonnegative, under the same diagonal-action,
upper-bound and reversing-point assumptions. Strict positivity, the exclusion
of global line stability and the adelic chamber theorem remain separate
obligations.
