# Scalar Fourier orbits and complementary block orbits

This internal derived prerequisite connects the same full-matrix Schwartz
test on the Fourier and original sides, in actual signed Weyl coordinates.
It retains the supplied self-dual scalar Haar measure and the existing
integral-normalized unipotent Haar measure.

The definitions `signedWeylOrbitFourierKernel` and `signedBlockOrbitKernel`
use the inverse standard Whittaker character. The first evaluates the actual
plus rectangular Fourier transform at
`iota(u) w⁻¹ diag(a,1,...,1) h`. The second evaluates the original test at
`u M(a,X) w' iota(h)`, where `M` is the actual first-column affine matrix
and `X` has `m` rows and one column. At an invertible scalar, the latter is
the literal `blockMatrixAt m 0`, as proved by
`signedBlockOrbitKernel_at_generalLinear`. Both definitions allow zero
scalars.

Inverse transpose fixes the leading sign diagonal and the signed
complementary Weyl representative. The normalized determinant norm of the
latter is one: the alternating and leading sign diagonals have order two,
and the remaining factor is a permutation matrix.

`signedWeylOrbit_blockOrbit_fourier_duality` assumes a canonical p-adic
field, arbitrary nontrivial unitary additive character, the supplied
self-dual Haar measure, every natural `m` including zero, and normalized
determinant norm one for `h`. It proves genuine integrability of both
full product kernels and equality of their integrals. The proof specializes
the affine Fourier identity to `w' h`. On its Fourier side the inverse
`w'` cancels; on its original side inverse transpose yields `w' iota(h)`.
The remaining scalar sign `(-1)^(m+2)` is removed by a measurable
involution preserving the exact supplied scalar Haar measure. This
transports integrability as well as the integral, with no normalization
factor.

`signedWeylOrbit_blockOrbit_fourier_duality_averaged` applies Fubini to
those proved product integrabilities. It proves integrability of both
unipotent averages over their outer scalar or scalar/block variables and
equates the scalar-outer Fourier integral with the scalar/block/unipotent
iterated original integral.

The provenance is internal: WeylBlockFourier supplies the actual affine
Fourier theorem and block coordinates; WeylSigns supplies the explicit
signed matrices; FourierInvariance supplies finite-order and permutation
determinant norms. This module proves no spectral-weight comparison,
compact-kernel integration, same-model dual-vector extraction, or final
gamma equation. Those remain further obligations of the host task.
