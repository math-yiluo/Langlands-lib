# Complementary dual value with the original box constant

This internal derived module composes the actual signed model realization,
principal-fixed pairing, measure-preserving signed Fourier transport and
literal quotient dual transport. It keeps the same original model vector,
principal level, arbitrary character, supplied self-dual additive Haar measure,
and compatible rank-one quotient measure.

`principalDual_value` assumes genuine integrability of the raw Fourier matrix
integrand and of the complete complementary block product. The signed dual of
the original vector is realized in the actual inverse-transpose pullback
coefficient image, whose representation is smooth. Its principal invariance
holds at the same level. The principal pairing then gives the original box
extraction constant, and the two exact transports identify its sides with the
raw inverse-transpose matrix value and `dualUnequalRankModelIntegralAt`.
Fubini is used only through the block value theorem with its genuine product
integrability hypothesis. No extra sign, character or measure factor occurs.

`PrincipalDualAssertions` records a common right half-plane for genuine raw
Fourier matrix convergence and the complementary value of the inverse-transpose
of the original realization's averaged coefficient. The constant is the same
box extraction constant used by the original comparison. The assertion is for
each supplied full-matrix Fourier partner of that precise box.

`principalDualAssertions_of_rawConvergence` takes an actual principal realization,
full Whittaker type, a nonzero functional, the supplied matrix convergence and
inverse-transpose analytic data, and genuine raw Fourier convergence on a right
half-plane. The data give a common genuine complementary-block half-plane.
The existing original comparison supplies original raw matrix convergence.
Full-test Fourier covariance transfers the compact stabilizer to the Fourier
partner. The paired normalized-average theorem then transfers the two raw
values to the very same averaged coefficient. Taking the maximum of the three
bounds and applying `principalDual_value` proves the assertion.

The provenance is the published principal pairing, actual realization,
signed/quotient transports, complementary-block convergence and paired
normalized-average lemmas. The convergence wrapper retains an explicit raw
Fourier convergence premise. It does not assert that premise follows from the
matrix data and does not prove the final gamma functional equation.
