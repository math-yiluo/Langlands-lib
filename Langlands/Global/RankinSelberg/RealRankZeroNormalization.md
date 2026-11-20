# Entire normalized ordinary integrals for real GL₁ × GL₁

The original real Tate integral divided by its Gamma factor is analytic
for positive real part of the Tate parameter. On the half-plane where the
reflected Tate integral converges, the reflected quotient with the inverse
phase is analytic. The proved Tate identity gives equality on the overlap,
so the two formulas define the entire `RealTate.normalizedZeta`.
`normalizedZeta_gaussian` applies the real Tate Gaussian calculation and
the identity principle to show that this normalized value is one.

`exists_normalized_realEqualIntegral` transfers the entire normalization to
the actual real ordinary quotient integral in rank one. It uses the proved
quotient Haar comparison with a positive multiple of the Haar measure on
real units, and the rank-one formula identifying the pair Gamma denominator
with the Tate denominator for the product character. The same constant
measure and Whittaker normalizations multiply the Tate zeta function and
its entire normalization.

For two nonzero rank-one Whittaker functions, the parity-adapted Gaussian
can be rescaled by the inverse of those constants. The resulting
Schwartz test realizes the pair L-factor on the initial half-plane.

The source is H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009),
formula (2.6) and Theorem 2.1(ii), pp. 6–7 in the author-posted version,
after specializing to rank one, and the real Tate normalization in Appendix
16.1, pp. 109–110. The registered file `jacquet-2009-archimedean-rankin-selberg`
has SHA-256 `7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.
The Lean proof follows the published `RealTateProof` Fourier convention.
