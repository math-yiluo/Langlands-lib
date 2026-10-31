# Actual unipotent-coordinate Fourier inversion

Author: Worker 623.

This internal coordinate calculation combines the published complementary affine
Fourier identity and the exact lower and upper parametrizations. The field is
locally compact, second countable, Hausdorff and totally disconnected, with its
Borel measurable space and topological ring structure. The supplied scalar
additive Haar measure is sigma finite and self-dual for the supplied character.
All sizes, including size one, are included.

Write `C(a)` for `cyclicShiftMatrix n a`, with negative superdiagonal and final
first-column entry `a`; write `M(v)` for `firstColumnMatrix n v`. For the actual
upper-unipotent element `u`, put `s(u)` equal to the sum of its adjacent upper
entries. `unipotentCoordinate_fourier_duality` proves absolute convergence and

    integral_(X,a) psi(s(u)) PhiHat(u^transpose C(a))
      = integral_(X,v) psi(-s(u)) Phi(u M(v)),

where `u` is the actual inverse entry-coordinate homeomorphism applied to `X`.
The measure on `X` is the product of the supplied scalar Haar measure over all
strict-upper entries; the other factors are the supplied scalar Haar on `a`
and its row product on `v`.

The lower parametrization has trailing diagonal `-u_(i,i+1)`, and the upper
parametrization has superdiagonal `u_(i,i+1)`. These identities turn the phases
of `shiftedTriangular_fourier_duality` into the displayed character phases.
Both parameter maps preserve measure exactly. Pullback of the actual
integrable functions therefore proves absolute convergence and transports
their integrals. No arbitrary normalization of group Haar is identified with
the coordinate product. This lemma alone does not prove a weighted Whittaker
pushforward or the same-vector gamma comparison.

`unipotentHaar_transpose_fourier_duality` proves the same formula and both
absolute convergence assertions using any actual Haar measure `mu` on the
upper-unipotent group, with its Borel measurable space. Haar uniqueness gives
`mu = c * map(coordinate product)` for a finite nonnegative scalar `c`.
For each auxiliary measure, the product of the entry homeomorphism with the
identity carries the coordinate product to the group product. Scaling the
measure preserves integrability and multiplies its integral by the same `c`.
Applying this to both sides of the coordinate identity proves the actual group
Haar identity. In particular, its proof does not set `c` to one or choose a
new scalar Haar measure. The left matrix is a transpose; replacing the group
variable by its inverse to obtain inverse-transpose is a separate step.
