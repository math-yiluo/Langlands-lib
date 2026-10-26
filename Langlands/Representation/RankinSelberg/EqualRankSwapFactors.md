# Universal epsilon and gamma certificate exchange

This module lifts the fixed-functional transport to the existing
equal-rank factor relations. For any specified nonzero target functionals,
translate them by the minus-one diagonal to obtain the source functionals.
The translations are involutive and preserve nonzero functionals, so the
universal tests cover every target functional pair. The supplied source
certificate retains its compatible-quotient-measure existence witness.

Whittaker type for the original first representation supplies its minus-one
scalar. The source equation already supplies the second scalar. The checked
functional-equation transport then proves the target equation at the same
additive character, Haar measure, epsilon monomial or gamma function.
Applying the argument in both orders gives each iff.

For canonical p-adic fields, the published character-change quotient-measure
theorem supplies the required law for each compatible quotient measure. The
helper theorems allow an arbitrary supplied additive Haar measure; no
self-duality premise is needed because each Fourier pair is retained.

This is the direct transport proof of the symmetry asserted for epsilon by
JPSS (1983), Section 2.12, printed page 403 (PDF 38), registered source
`jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Gamma symmetry is derived here directly from the defining equation, rather
than using the ratio formula of Section 3.1(2). No analytic theorem, factor
existence, irreducibility or smooth-contragredient identification is assumed.
The exact closed conjunction is assembled in `EqualRankFactorSwapProof`.
