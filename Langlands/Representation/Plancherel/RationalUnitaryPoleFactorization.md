# Factoring monomial denominators for actual unitary pole cancellation

`RationalUnitaryPoleFactorization` records an equality between a given
actual regular scalar and the product of a list of actual coordinate
roots times a remainder. The remainder is nonzero at every unitary
parameter. Multiplication concatenates the lists and multiplies the
remainders.

For a nonzero valuation-lattice exponent, a monomial minus a constant
on the unit circle splits into a list of actual coordinate roots by
`rationalUnramifiedLatticeMonomial_sub_factorization`. If the constant
is off the circle, the binomial is itself nonvanishing on the unitary
subgroup. The constructor for a list of binomials iterates these two cases
and includes any initial factor already nonvanishing on that subgroup.

`exists_regularGermAt_of_poleFactorization` takes such a factorization
of the original whole-operator denominator, together with the cleared
identity for the actual generic comparison, nonvanishing on the genuine
generic locus, and the cleared unitary bound. It uses the existing
cancellation theorem to give a regular germ of that comparison at
every unitary parameter.

This connects the supplied monomial factorization to the cancellation
argument of Waldspurger (2003), Corollary V.2.3 and Lemma V.3.1, printed
pp. 294–295 / PDF pp. 60–61 (`waldspurger-2003-plancherel`). The factor
support and bound of a standard-family denominator are analytic inputs.
