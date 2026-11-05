# Conditional assembly of the actual centralizer-parahoric intersection

This derived interface works over every nonarchimedean local field `F : Type u`,
in either characteristic, with the supplied actual zero and building data.
`CentralizerParahoricAssemblyStatement` says that actual root-group lifting,
singleton sharp-fixer boundedness, and the cover-image centralizer comparison
together imply the unchanged `CentralizerParahoricIntersectionStatement`.
The module proves this implication, and an equivalence of the two algebraic
centralizer comparisons. It does not prove the three inputs.

## Algebraic comparison

`centralizerZeroIntersection_of_coverImage` proves that
`CoverImageCentralizerNormKernelStatement` implies
`CentralizerZeroIntersectionStatement` for every `E : ZeroSubgroupDatum i j`.
The reverse implication is already published in `KPMinimalLeviZeroStatement`;
`coverImageCentralizerNormKernel_iff_intersection` combines the directions.

For the new direction, take `z` in the full intersection. The published
`mem_zeroSubgroup_iff` gives
`j(z) = c * j(z₀)`, with `c` in the actual simply connected image and
`z₀` in the actual `E.centralizerZero`. Thus `j(z * z₀⁻¹) = c`.
Both `z` and `z₀` belong to the rational-character norm kernel, using the
published inclusion for `z₀`. Subgroup closure puts `z * z₀⁻¹` in that
kernel. The assumed cover-image comparison now puts it in
`E.centralizerZero`; multiplying by `z₀` recovers `z` in the same subgroup.
The other inclusion is the already published
`centralizerZero_le_zeroSubgroup_comap_inf_normKernel`.

This uses the actual product interpretation of the existing join, whose proof
uses normality of the actual cover image. It does not assume normality or
independence of all zero data, or replace a zero subgroup by a norm kernel.

## Conditional building assembly

`centralizerParahoricAssembly` uses the published
`centralizerParahoricReduction` to reduce the exact target to a singleton
sharp-centralizer inclusion under the same apartment axioms. A point in that
intersection lifts to an actual point `z` of the supplied represented
centralizer. Actual root lifting puts its sharp image in the supplied simply
connected image. The published boundedness adapter
`comap_sharpFixer_le_centralizerNormKernel` puts `z` in the centralizer's
rational-character norm kernel. The assumed cover-image comparison puts
`z` in the actual centralizer-zero subgroup, giving the required image witness.

`centralizerParahoricIntersection_of_minimalLeviComparison` supplies that last
comparison from the intersection conjunct of the published
`MinimalLeviZeroComparisonStatement`. It remains conditional on that statement,
root lifting and singleton sharp-fixer boundedness.

## Provenance and scope

These are internal deductions from the published definitions and reductions,
not additional numbered results attributed to the literature. Their role is to
assemble the algebraic cover comparison, the boundedness argument and the
singleton reduction for KP Lemma 7.4.3. All imported Lean/Markdown pairs and the
final target are unchanged. The actual centralizer map, torus, cover, zero
subgroup, root subgroups and sharp fixers are retained.

The three substantive inputs remain separate proof obligations. This module
does not supply an unconditional proof of KP Lemma 7.4.3, rational surjectivity
of the cover, or an equality of zero and norm-one subgroups in general.
