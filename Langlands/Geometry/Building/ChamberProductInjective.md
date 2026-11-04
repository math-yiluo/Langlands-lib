# Injectivity of the sharp and full chamber products

This internal supporting construction equips the two existing three-factor
multiplication maps with embeddings into the unchanged group of rational points.
The sharp version applies to any actual apartment data over a field in universe
`u`, every subset `C`, every apartment point `x`, and every cocharacter `ν`. The
full version applies to any actual `ParahoricBuildingData`, every subset `C` and
every cocharacter. Neither result requires chamber geometry, genericity or the
apartment axioms.

The central factors remain, respectively, `D.sharpCentralizer {x}` as a subgroup
of `G(k)`, and `P.centralizerZero = Z(F)^0`, mapped to `G(F)` by the actual
centralizer inclusion. The underlying functions of the embeddings are exactly
`sharpUnipotentProduct` and `iwahoriUnipotentProduct`.

The implemented proof is intrinsic to the published Dynamic and centralizer
interfaces. The general restriction lemma `unipotentTripleProduct_injective`
allows arbitrary negative and positive subgroups contained in the corresponding
Dynamic unipotent groups, and an arbitrary injectively mapped central factor
whose image lies in `centralizerPoints i`. The image of the central factor lies
in the Dynamic centralizer and hence in the Dynamic parabolic. Opposite-cell
injectivity distinguishes the negative factor from the product of the other
two factors. The latter product has its central factor as its limit under the
cocharacter, because the positive factor contracts to the identity. Uniqueness
of limits for the affine, hence separated, ambient group identifies the central
factors; cancellation identifies the positive factors.

For the sharp map the required inclusions are the first components of the
published intersections. For the full map the same unipotent inclusions apply;
`map_mem_centralizerPoints` supplies centralizer membership and the actual
centralizer's representing monomorphism supplies injectivity on rational
points. The identity between negation in the cocharacter lattice and reversal
of the multiplicative parameter is the published
`groupHom_neg_comp_eq_oppositeCocharacter`.

This unit proves injectivity only. The exact ranges, equality of full and sharp
unipotent intersections, normalizer and central intersections, and ordered root
block bijections in `ChamberIwahoriDecompositionStatement` remain separate
obligations. No source factorization assertion is assumed in the construction.
Its provenance is the proof above using the existing Library definitions and
proved opposite-cell and limit theorems; it makes no additional literature
claim.
