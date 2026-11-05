# Centralizer-zero conjugation by the simply connected normalizer image

This is an internal derived intermediate construction on the actual
`ParahoricBuildingData P`. It keeps
`P.zeroDatum.CoverImageCentralizerNormKernelStatement` as an explicit hypothesis.
It does not prove that comparison or the closing affine Iwahori–Tits statement.

For an actual normalizer point `n` whose rational-point value belongs to
`P.simplyConnectedImage`, conjugation preserves the full subgroup
`P.centralizerZero.map (rationalPoints.map P.centralizer.j)`. The conclusion is
first a forward membership implication, then actual subgroup normalization and
equality under the map induced by ambient conjugation.

For a point `z` in the actual centralizer-zero subgroup, form
`c = n * j(z) * n⁻¹ * j(z)⁻¹`. Normality of the published actual simply connected
image puts `c` in that image. Normalizer conjugation preserves the actual
centralizer, so the represented centralizer supplies a rational point `w` with
`j(w) = c`. Centralizer-zero points and their inverses fix the apartment by the
published norm-kernel inclusion and omega compatibility. Thus `c` fixes every
apartment point. The published centralizer norm-one fixer lemma, together with
the norm-kernel inclusion for the simply connected image, puts `w` in the
centralizer's rational norm kernel. The explicit cover comparison gives
`w ∈ P.centralizerZero`. Finally `n * j(z) * n⁻¹ = j(w) * j(z)` proves forward
preservation. Applying it to `n⁻¹` gives the reverse implication.

`centralizerZeroSCNormalizerAut` restricts the literal ambient conjugation
equivalence to the mapped centralizer-zero subgroup using this equality. Its
coercion theorem states its value as `n * g * n⁻¹` in the original rational
group.

The final specialization takes a supplied opposite factor pair for a
nonidentity actual root point. Under `P.SatisfiesApartmentAxioms`, the published
reflection-element cover-image theorem places its actual representative in the
simply connected image, so the same normalization conclusion applies. No
rank-one factor-pair existence hypothesis is used. Normality of
`P.normalizerZero` in the whole normalizer remains a separate obligation.

The provenance is internal deduction from the actual normalizer and represented
centralizer, the published normality of `simplyConnectedImage`, the norm-kernel
inclusions, and the centralizer norm-one fixer lemma. There is no new
literature assertion.
