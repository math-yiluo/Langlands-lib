# Integral inner-twisted maps for actual unramified stabilizer models

This is an internal specialization of `InnerSemilinearExtension` and
`UnramifiedTwistedPointStabilizer`. All coefficient types have arbitrary common
universe `u`. Let `F` be a nonarchimedean local field and `K` its actual inertia
fixed field in the separable closure. Let `G` be an affine `F`-group, `B` supplied
upstairs building data for `G_K`, and `A` supplied semilinear apartment data for
`B`. Let `c` be an actual rational-point cocycle for coefficient conjugation.
Assume `y` is fixed by every twisted building permutation.

Let `P` be a supplied integral model of `G_K` over the actual integer ring
`fixedFieldIntegers F`, with integral-point image exactly `B.oneStabilizer y`.
This is the full character-valuation-kernel point stabilizer, with no
identification with a neutral parahoric.

`twistedStabilizerModel_points_stable` proves that
`g ↦ c σ * rationalConjugate σ g * (c σ)⁻¹` preserves the integral-point image.
It uses the published transport equivalence for the actual stabilizer and the
twisted fixedness of `y`. The inverse-stability theorem uses the same
equivalence: applying the forward map to
`rationalConjugate σ.symm ((c σ)⁻¹ * g * c σ)` gives `g`, by coefficient
inversion and group cancellation.

For smooth `P`, `twistedStabilizerModelIso` constructs an actual compatible
isomorphism from its coefficient twist to `P`, using the actual integer
automorphism `fixedIntegerBaseAut F σ`. Its generic comparison is the canonical
coefficient comparison followed by inner conjugation by `c σ`. The construction
applies `innerGaloisTwistIso`, the two point-stability theorems, and
`fixedField_hasSmoothHomExtension smoothHomExtension F`. Thus the general
extension premise is discharged by the proved arithmetic and strictly Henselian
homomorphism-extension theorem.

`twistedStabilizerModelIso_integralPointMap` records the exact inner-twisted
evaluation of the extension on the coefficient pullback of each original
integral section. `twistedStabilizerModelIso_generic_comm` records its full
generic compatibility square. Both specialize the corresponding theorems of
`InnerSemilinearExtension`.

This unit assumes the model and its exact integral-point identification; it does
not establish their existence. It constructs individual isomorphisms for every
coefficient index, without claiming family coherence, effective descent, a
reductive residue quotient, Frobenius comparison, or a chamber assertion.
