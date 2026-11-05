# Actual archimedean points of a number-field Weil restriction

Author: Worker 112.

For a number field `F` in universe zero, this file constructs the canonical
`F`-algebra isomorphism `realTensorEquiv F : F ⊗[ℚ] ℝ ≃ₐ[F] InfiniteAdeles F`.
It then constructs the multiplicative equivalence `realPointsEquiv F G` from the
actual real points of `AffineWeil.groupScheme ℚ F G` to the original
infinite adelic points `InfiniteAdelicGroupPoints F G`. Here `G` is an affine
group scheme over `F` that is locally of finite type.

## Coefficient isomorphism

- `liesOver_ratInfinitePlace` proves that every infinite place of `F` lies over
  `Rat.infinitePlace`. The restriction `v.comap (algebraMap ℚ F)` is an infinite
  place of `ℚ`, and `ℚ` has only one infinite place. The file uses this only as
  a local instance.
- `realRatCompletion : ℝ ≃ₐ[ℚ] Rat.infinitePlace.Completion` is the inverse of
  Mathlib's completion-to-real ring isomorphism at the real place of `ℚ`. It is
  continuous because that isomorphism is an isometry.
- `completionMap_realRatCompletion` says that the completion map from
  `Rat.infinitePlace.Completion` to `v.Completion`, composed with
  `realRatCompletion`, equals the existing `PositiveRealIdeles.realEmbedding F v`.
  Both maps are continuous ring maps on `ℝ` and agree on rationals. Since `ℚ` is
  dense in `ℝ`, they are equal.
- `aboveRatProductEquiv` reindexes the product over places above the rational
  infinite place as the product over all infinite places of `F`.
- `realTensorRingEquiv` is the composite of the following maps:
  1. tensor commutativity;
  2. `realRatCompletion` tensored with the identity of `F`;
  3. the published completed tensor decomposition
     `AdelicFunctoriality.infiniteTensorEquiv` at `Rat.infinitePlace`, whose
     bijectivity comes from weak approximation and the local-degree sum;
  4. the reindexing above.
- `realTensorRingEquiv_tmul` and `realTensorEquiv_tmul` give the coordinate
  formula: at each infinite place `v`, the tensor `x ⊗ r` goes to
  `algebraMap F v.Completion x * PositiveRealIdeles.realEmbedding F v r`.
  This holds at complex places too, where `ℝ` embeds in `v.Completion`.
- `realTensorEquiv` is this ring isomorphism made into an `F`-algebra
  isomorphism. With `r = 1`, the coordinate formula shows that it commutes with
  the algebra maps from `F`.

## Point comparison

`realPointsEquiv F G` composes two maps. The first is the published
multiplicative `AffineWeil.pointsEquiv ℚ F G ℝ`, from real points of the
restriction to `G`-points with coefficients in `F ⊗[ℚ] ℝ`. The second is the
original group's affine-point functor applied to `realTensorEquiv F`.
`realPointsEquiv_apply` says, by definition, that it is the tensor-valued point
map followed by the affine point map of that coefficient isomorphism.

## Scope

The construction adds no smoothness, reductivity, splitness or commutativity
hypothesis. It asserts no topology, continuity, measure or finite-adele
comparison. It does not identify any split centre, and it does not claim that a
greatest rational split central torus exists. It is an internal construction
that combines published Library results and Mathlib. It makes no new external
mathematical claim.
