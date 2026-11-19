# Monomial binomials on the actual unramified character torus

`rationalUnramifiedLatticeMonomial` is the regular scalar indexed by an
element of the actual valuation image. It uses the published coordinate
algebra equivalence and evaluates as the unramified character at any lift
of the exponent. Its absolute value is one at every unitary parameter.
Consequently subtracting an off-circle constant gives a factor that is
nonzero throughout the unitary subgroup.

For a nonzero exponent and a constant on the circle,
`rationalUnramifiedLatticeMonomial_sub_factorization` expresses the binomial
as a finite product of the existing actual basis-coordinate roots. Smith
normal form for the rank-one span of the exponent writes it as a positive
integer multiple of the first vector of an integral basis, after reindexing
and choosing the sign of the basis. The monic complex polynomial obtained
by subtracting the constant from the corresponding power of one variable
splits. Every root has absolute value one. Evaluation at the basis monomial
then gives the factorization in the original regular scalar algebra.

This algebraic step supplies coordinates for monomial pole factors in the
route of Waldspurger (2003), Corollary V.2.3 and Lemma V.3.1, printed
pp. 294–295 / PDF pp. 60–61 (`waldspurger-2003-plancherel`). Applying it to
a standard intertwiner requires a denominator expressed using such factors.
