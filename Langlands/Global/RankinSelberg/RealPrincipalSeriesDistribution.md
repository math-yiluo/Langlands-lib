# The test distribution of a real principal-series Whittaker functional

The normalized inducing character is the product of the signed complex powers
of the diagonal entries of the actual upper triangular group. The diagonal
entries are nonzero, so `positionBorelCharacter` takes values in complex units.
The normalized character identity identifies this product with the Library's
principal-series character on a diagonal followed by an upper unipotent.

`averageMap` sends a complex smooth compactly supported test on the open set of
invertible matrices to a smooth inducing section. It integrates left translates
of the test against right Borel Haar weighted by the inverse inducing character.
Right invariance supplies the inducing transformation law. The compact
right-derivative bounds on a linear functional give a bound on its composite with
the average by a finite sum of norms of continuous test maps. The composite is
therefore continuous and restricts to a complex-valued distribution on real tests.

If the inducing functional transforms under the upper unipotents by the specified
Whittaker character, the distribution has that covariance under right pullback.
Indeed, right translation commutes with the average. On the left, the upper
unipotents preserve the chosen right Haar measure and the inducing character is
trivial there, giving invariance. `RealPrincipalSeriesDistributionStatement`
records these two laws for the constructed distribution. This is an internal
step in applying Bruhat support descent to smooth Whittaker functionals.
