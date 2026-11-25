# Truncated polynomial test algebras and nilpotent points

This internal infrastructure supplies the
finite polynomial test algebras used to reconstruct actual formal
power-series maps from natural families on nilpotent points. The base
is an arbitrary commutative ring R.

`boxIdeal R sigma m` consists of polynomials whose coefficients vanish
at every exponent whose entries are all less than m. It is an ideal:
in a contribution to a product coefficient inside the box, each
factor's exponent is itself inside the box. Its quotient
`BoxAlgebra` therefore retains exactly the coefficients inside that
box. An exponent outside it gives a vanishing quotient monomial.

A tuple whose coordinate m-th powers vanish defines an actual
R-algebra map from this quotient by polynomial evaluation. For finite
sigma, `truncBox` is the finite polynomial consisting of the power
series coefficients inside the box. Evaluation of a pointed formal
map on such a tuple agrees with evaluation of its box truncation:
all contributions outside the box vanish.

The quotient's coordinate variables give the universal nilpotent
`boxPoint`. Every tuple killed coordinatewise by a common m-th power
is its image under the evaluation map. Universal points agree under
the quotient transitions between boxes. The m = 1 point is zero.
Finiteness of the coordinate set gives a common annihilating power
for every actual nilpotent tuple.

The file also proves that points with no formal variables are
determined by their constant coordinates. These constructions are
internal, not an external theorem quotation, and support the actual
point-to-formal-map step in `LocalQuasiIsogenyInverseStatement`.
