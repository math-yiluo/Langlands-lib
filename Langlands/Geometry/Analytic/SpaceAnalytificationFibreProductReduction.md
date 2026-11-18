# Conditional reductions for analytification fibre products

Author: Worker 790.

This module proves conditional reductions of the published
`SpaceAnalytificationFibreProductStatement`. It does not prove that
proposition without the additional hypotheses listed below. The field
is complete, ultrametric and nontrivially normed throughout, and all the
results hold in every field universe `u`.

It imports the conditional gluing lemmas in `EtaleHomGluing`. The
`hom_ext_of_etale_local_eq` proof and its hypotheses are documented there.

`IsAnalytification.hom_ext` applies this lemma to the jointly surjective
étale affine test maps in `IsAnalytification`. Equality is tested on
complete analytic morphisms on these charts, not merely on point maps.

`compatible_square_commutes` rewrites a pair of composites on every
affine test map using the four compatibility equations. The algebraic
commuting equation equates the resulting test points, and the preceding
uniqueness lemma gives commutativity in the localized analytic category.
No separatedness or local finite type assumption is needed for this
commutativity reduction.

`isPullback_of_joint_monic` combines commutativity, the pointwise étale
local existence theorem of `SpaceAnalytificationLocalLifts`, and the
Hom-sheaf gluing theorem. It assumes the actual Hom-sheaf property,
localized étale base change, lifting of matching points through localized
pullbacks, and joint monicity of the two analytic projections. It proves
that this analytic square is a categorical pullback. The algebraic base
is assumed separated for the affine intersection used in local existence.
The theorem does not discharge these four additional premises and is
therefore a conditional reduction, not an exact proof of the published
fibre-product statement.

`fibreProductStatement_of_affine_and_etale_inputs` supplies this joint
monicity using `SpaceAnalytificationJointMonicity`. In every universe it
returns the unchanged published `SpaceAnalytificationFibreProductStatement`
from five explicit inputs: the actual étale Hom-sheaf property, the
published affine tensor-product preservation proposition, localized affine
functoriality, localized étale base change, and lifting of matching
underlying points through localized pullbacks. It proves no one of those
inputs and therefore remains a conditional reduction. The bridge in
`SpaceAnalytificationAffinePullbacks` converts tensor preservation to the
spectrum-map form needed for joint monicity.

`fibreProductStatement_of_affine_and_descent_inputs` discharges the
localized affine functoriality premise using the published theorem
`AffineAnalytification.affineAnalytificationLocalizedFunctoriality` from
`AffineAnalytificationLocalizedFunctorialityProof`. The proof and its
Markdown were checked against the published Library. This leaves four
explicit premises: the actual étale Hom-sheaf property, affine tensor
preservation, localized étale base change, and matching-point lifting.
The original five-input reduction remains available. The new corollary
also remains conditional and does not prove the exact target without
those four inputs.

The Hom-sheaf premise is written out inline: for every field with the
hypotheses above and all localized analytic spaces `S` and `T`, the
presheaf obtained by restricting `Hom(-, T)` to the small étale site of
`S` is a sheaf. The matching-point premise asserts existence, for every
categorical pullback in `LocalizedCategory.{u,u,u}`, of a point over each
compatible pair of points in the two factors. It asserts neither
uniqueness of that point nor a topological pullback property.

`FibreProductReductionStatement` is the Prop-valued definition of the
remaining three-input implication. Its first premise is the actual
Hom-sheaf property just described, its second is
`AffineAnalytificationFibreProductStatement.{u,u,u,u}`, and its third is
localized étale pullback existence with étale base change for every field
with the stated hypotheses. Its conclusion is the unchanged
`SpaceAnalytificationFibreProductStatement.{u}`. It does not assert that
any of these premises holds.

`fibreProductReduction` proves this implication. It applies the preceding
four-input corollary and supplies the matching-point premise using the
published `SaturatedAtlasPresentation.exists_point_of_isPullback` from
`LocalizedPullbackPoints`. That theorem applies to arbitrary categorical
pullbacks and compatible underlying points in the equal-universe
localized category over a complete ultrametric normed field. Its
existence-only conclusion is exactly the premise used here; no uniqueness
or topological pullback claim is needed. The published theorem and its
Markdown were read and compared with the current Library. Thus
localized affine functoriality and matching-point lifting are discharged,
and the other three premises remain explicit. This still does not give
an unconditional proof of the exact target.

## Provenance: internal

These are direct categorical and algebraic consequences of the published
`IsAnalytification` definition and the explicitly stated analytic inputs.
The local existence, affine comparison and joint monicity constructions
are implemented in the accompanying helper modules. All new or
unproved geometric inputs remain hypotheses; no unpublished statement or
proof is imported. The analytic inputs discharged here are localized
affine functoriality and matching-point lifting, via their published
proofs. This is a supporting
reduction for the fibre-product proof task, not its unconditional
exact-target theorem.
