# A finite smooth-coefficient envelope on the full diagonal torus

This is an internal consequence of smooth simple-root support and the published
smooth-dual realization on the antitone torus cone. It adapts the support-shift
argument in `SquareIntegrableWhittakerTorusSumProof`, without using its
square-integrability hypothesis or conclusion.

For any smooth representation, Whittaker functional and vector,
`TorusCoefficientEnvelope` asserts that finitely many actual bi-smooth matrix
coefficients bound the norm of the Whittaker coefficient at `diag(a) κ`, for
every diagonal `a` and every integral general linear matrix `κ`. The coefficients
are evaluated at the same diagonal `diag(a)`. There is no analytic hypothesis.

The proof chooses a uniformizer. Simple-root support gives a fixed shift of all
nonzero torus values into the antitone cone. The integral subgroup has a finite
orbit on the smooth vector. For each orbit vector, the published principal
average supplies a smooth functional agreeing with the Whittaker functional
on the shifted cone. Moving the shift to the vector shows equality with a
smooth coefficient at the original torus element whenever the Whittaker value
is nonzero. Every diagonal is a uniformizer power times an integral diagonal.
Taking every pair from the finite integral orbit absorbs this integral diagonal
and the supplied integral factor. One term then agrees with the nonzero
Whittaker value, and the sum of all coefficient norms bounds it.

The result supplies a pointwise envelope only. It does not claim raw matrix
integrability or the final functional equation.
