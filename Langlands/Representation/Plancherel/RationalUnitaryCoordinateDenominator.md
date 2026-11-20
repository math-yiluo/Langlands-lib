# Pole factors for one-coordinate Laurent denominators

`RationalUnitaryPoleFactorization.ofFirstCoordinateLaurent` constructs
the unitary pole factorization of a nonzero Laurent polynomial pulled
back along the first coordinate of a supplied integral basis of the
valuation lattice. Multiplying by a power of the variable gives an
ordinary polynomial. Its complex roots, counted with multiplicity,
give binomials in the first valuation-lattice monomial. The leading
coefficient and the Laurent monomial used to undo the multiplication
are nonzero at every unitary character. The existing binomial
factorization puts the roots on the unit circle into the pole list and
the other factors into the unitary-nonvanishing remainder.

`RationalUnitaryPoleFactorization.ofSlice` uses this construction on
the scalar denominator specialized along a first-coordinate slice.
A single ambient character where the specialized scalar is nonzero
certifies that its one-variable Laurent polynomial is nonzero.

These are algebraic reductions for the coordinate dependence discussed
after IV.1(13) and the unitary pole argument of Corollary V.2.3 and Lemma
V.3.1 in Waldspurger (2003), printed pp. 283 and 294–295 / PDF pp. 49
and 60–61 (`waldspurger-2003-plancherel`). The first-coordinate dependence
of a standard intertwiner is an input to the operator slice construction
that precedes this factorization.
