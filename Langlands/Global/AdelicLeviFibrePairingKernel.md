# Levi kernels for the transpose of fibre smoothing

Fix a standard parabolic \(P=MU\) in a compatible standard family over
a number field, a compactly supported continuous ambient kernel \(\beta\),
and a positive point map \(p\) from a split torus to the Levi.
`leviFibrePairingKernel` at \(g,b\) is the compactly supported continuous
Levi kernel
\[
  z\longmapsto L(g,p(b)z),\qquad
  L(g,m)=\operatorname{radicalKernel}(\beta,g,1,m).
\]
The compact support follows from the homeomorphism of left multiplication
by \(p(b)\). The Levi test function result assumes the adelic test
property for \(\beta\) and the normalized radical average proposition.
It applies `isAdelicTestFunction_radicalKernel`, which accounts for
the Haar normalization, then uses stability under Levi translations.

For central \(p\), `normOnePartialConvolution_leviFibrePairingKernel_mul_positive`
replaces \((g,b)\) by \((\iota(p(a))g,ab)\), where \(\iota\) is the Levi
inclusion. Left-Levi covariance contributes the factor \(\delta(p(a))\).
The remaining positive factor \(p(b)\) commutes with the Levi arguments
and can be moved to the right of the evaluation point. The resulting
partial convolution uses \(L(g,-)\).

`integral_leviFibreSmoothingIntegrand_mul_conj` fixes \(g,b\), uses the
central split torus comparison of the norm-one and positive rational
quotients, and assumes right invariance of norm-one Haar. It pairs the
smoothed evaluation of a Levi \(L^2\) class against a bounded measurable
test on the norm-one rational quotient. The two kernel conjugations in
smoothing cancel, so the kernel becomes \(L(g,p(b)x^{-1}y)\).
Transport preserves the exact norm-one quotient Haar scale. Finite
norm-one quotient volume makes the pulled-back \(L^2\) representative
integrable, and the restriction of the kernel to the closed norm-one
subgroup has compact support. The quotient kernel transposition then
gives the integral pairing the original class against the partial
convolution of the transported test with `leviFibrePairingKernel`,
with the inverse modulus kept as a scalar.

These internal formulas use the parabolic Iwasawa kernel of
Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein Series*,
I.1.13, and the norm-one pairing of Bernstein–Lapid, *On the
meromorphic continuation of Eisenstein series*, §6.2, equation (6.8).
