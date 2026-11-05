# Actual centralizer-zero lifts of reflection squares

This derived module starts with a nonidentity point in an actual relative root
group and a supplied opposite factor pair. It proves that its literal
normalizer representative has square in the supplied centralizer-zero image,
under `P.SatisfiesApartmentAxioms` and the explicit intermediate comparison
`P.zeroDatum.CoverImageCentralizerNormKernelStatement`.

Valuation inversion identifies the affine reflection functionals of `u` and
`u⁻¹`: their values, viewed in `WithTop ℝ`, are the same at every apartment
point. Reversing and inverting an actual opposite pair gives a pair for `u⁻¹`,
and its literal product is the inverse representative. Applying
`reflectionElement_inv_mul_eq_centralizerZero` to these two pairs therefore
gives a centralizer-zero point mapping to `m(u)⁻¹ m(u)⁻¹`. Inverting that point
gives an actual preimage of `m(u)²`.

`reflectionSquareCentralizerZero` chooses such a point in the original
`P.centralizerZero`. Its image formula records equality in the original rational
group. The final corollary places the literal square in `P.normalizerZero`,
the published image of the same centralizer-zero group in the normalizer.

The construction and proofs are internal deductions from the imported
valuation-inversion, pair-inversion, same-jump correction, and zero-subgroup
definitions. They require no factor-pair existence assumption and apply to each
supplied pair. The cover comparison remains an explicit intermediate premise;
this module does not establish it or the closing Iwahori–Tits theorem.
