# Weyl and rectangular coordinates for the affine Fourier identity

This internal derived prerequisite rewrites the published actual unipotent
Fourier identity in signed Weyl and rectangular block coordinates. It uses the
plus transpose Fourier pairing and the supplied self-dual scalar Haar measure.
It does not assert the final gamma comparison or a same-vector dual extraction.

For every positive `n`, `cyclicShiftMatrix_eq_signedWeyl` identifies the
negative-superdiagonal cyclic shift with the inverse signed long Weyl matrix,
the diagonal with leading entry `(-1)^(n+1) a`, and the inverse signed
complementary Weyl matrix, in that order. The proof computes the unsigned
product entry by entry using the actual tail-reversal permutation, then
multiplies the explicit alternating and leading-sign diagonals. Thus it proves
the matrix identity rather than identifying the two representatives by definition.

For `n = m+1`, `signedWeylScalarFourierKernel` is the inverse standard
Whittaker character times the actual rectangular Fourier transform evaluated
at the inverse-transpose unipotent matrix, those three signed Weyl/diagonal
factors, and a fixed right translate `h`. The scalar ranges over the entire
field, including zero. `affineBlockFourierKernel` is the same inverse
Whittaker phase times the original test at the unipotent matrix times
`firstColumnMatrix`, with its row split into a scalar and an `m` by `1` block,
followed by the inverse transpose of `h`.
`affineBlockFourierKernel_at_generalLinear` identifies the latter matrix
pointwise with the literal `blockMatrixAt m 0` when the scalar is the entry of
a `GL_1` element. The multiplication order is retained throughout.

For every canonical p-adic field, every supplied self-dual `nu`, every natural
`m` (including zero), and every `h` of normalized determinant norm one,
`signedWeyl_affineBlock_fourier_duality` proves integrability of both full
product kernels and equality of their integrals. The Fourier side uses the
actual integral-normalized unipotent Haar measure times `nu.measure`. The
original side uses that same unipotent Haar measure times `nu.measure` times
the rectangular product measure induced by `nu`. There is no extra scalar or
Jacobian in the equality; the determinant norm condition on `h` is explicit.

The proof specializes the published
`padicUnipotentHaar_iota_fourier_duality_right` to the canonical topology and
actual unipotent Haar measure. It transports the original-side row measure by
the published measure-preserving `rankOneAffineParametersEquiv`, using its
product with the identity on the unipotent group. Measure preservation
transports integrability as well as the integral. Finally it rewrites the
negative adjacent-entry Fourier phase as the inverse standard character and
uses the proved signed Weyl identity. These are internal derivations from the
UnipotentIota, AffineBlocks and WeylSigns modules; no new literature claim or
functional-equation premise is used. Integration against model vectors,
weighted convergence for the dual average, and paired gamma extraction remain
further obligations.
