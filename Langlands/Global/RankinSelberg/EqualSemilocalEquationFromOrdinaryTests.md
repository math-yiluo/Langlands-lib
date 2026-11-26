# The equal-rank semi-local equation from ordinary archimedean tests

`realEqualPlaceFunctionalEquation` proves the equal-rank equation at a
real place for actual restrictions of global Whittaker functions.
`realPlaceUniformWhittakerModel` puts the two restrictions in the uniform
local models at scales \(a\) and \(-a\). In ranks above one,
`realLocalUniformPositiveEqualJacquet_of_continuation` combines convergence
and holomorphy with the proved local continuation and functional equation.
The dual denominator comparison and the real central scalar identify the
factors in the source convention. `realEqualFunctionalEquation_of_positiveJacquet`
converts the Fourier sign and adds the rank-one Tate case.

`equalSemilocalEquationFromOrdinaryTests` assumes ordinary nonvanishing at each
real and complex place in ranks above one. Each premise supplies a pair of
actual Whittaker restrictions, a Schwartz row test and compatible quotient
measure data, with nonzero ordinary integral arbitrarily far to the right.
The local functional equations supply dual nonvanishing for the same tests.
The actual Whittaker slice theorem and the positive-rank factorization reduction
assemble and integrate their ordinary and dual products, using Tate theory in
rank one. The real and complex equations and the central-sign comparison
then give the equal-rank semi-local equation for every number field in the
supplied field universe \(u\), with presentation universe \(uQ\).

The local equation uses the equal-rank case of H. Jacquet,
*Archimedean Rankin–Selberg Integrals* (2009), Theorem 2.1, author-posted p. 6.
The passage from local equations and factorizable tests to the partial
functional equation follows the equal-rank method in J. W. Cogdell,
*Analytic Theory of L-Functions for \(\mathrm{GL}_n\)* (2004), proof of
Theorem 4.1, printed pp. 219–220.
