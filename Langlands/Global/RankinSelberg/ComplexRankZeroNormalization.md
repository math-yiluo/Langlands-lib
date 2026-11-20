# Entire normalized ordinary integrals for complex GL₁ × GL₁

The complex Tate cross-product identity on the common strip, evaluated
with the angular Gaussian, identifies the original and reflected Tate
integrals after division by their Gamma factors and the Fourier phase.
The two formulas are analytic on overlapping half-planes. They define
`ComplexTate.normalizedZeta`, which is entire and has value one for the
angular Gaussian by the Gaussian calculation and the identity principle.

`exists_normalized_complexEqualIntegral` transfers this normalization
to the actual complex ordinary quotient integral in rank one. The Haar
comparison uses a positive multiple of multiplicative Haar measure on
complex units, and the factor of two converts this measure to the Tate
convention. The two Whittaker functions contribute their scalar values
and the product character. The reciprocal Gamma factor is the
published pair denominator for the two singleton parameters.

When both scalar values are nonzero, the angular Gaussian rescaled by
the inverse of the combined constant realizes the pair L-factor on
the initial half-plane.

The source is H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009),
formula (2.6) and Theorem 2.1(ii), pp. 6–7 in the author-posted version,
in rank one, and the complex Tate normalization in Appendix 16.1,
pp. 109–110. The registered file `jacquet-2009-archimedean-rankin-selberg`
has SHA-256 `7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.
The proof uses the trace Fourier transform and the public integral
identity and Gaussian lemmas used in the Library's complex Tate proof.
