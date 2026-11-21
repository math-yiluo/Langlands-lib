# Dominant monomorphisms into normal integral schemes

Let `f` be a quasi-compact dominant monomorphism locally of finite type
between integral schemes of the same arbitrary universe. Given
`HasNormalStalks` on the target, `normalizationIsoOfDominantMonoOfHasNormalStalks`
identifies Mathlib's relative normalization of the target in the source
with the target. Its forward map is `f.fromNormalization`.

The construction is internal. Dominance sends the generic point of the
source to the generic point of the target. The published generic-stalk
surjectivity for a monomorphism locally of finite type then identifies
the two function fields. Over each nonempty affine open of the target, the
source sections embed into that common field. Localizing the target
sections at maximal ideals gives the corresponding normal stalks, so the
target sections are integrally closed in the field. The integral closure
of the target sections inside the source sections therefore equals the
image of the target sections. This proves the normalization
identification on the affine opens, with the empty open handled separately.

Zariski Main Theorem gives the open immersion into the relative normalization.
Composing with the identification proves
`isOpenImmersion_of_dominant_mono_of_hasNormalStalks`. The construction
applies over arbitrary integral bases, including non-Noetherian ones.
