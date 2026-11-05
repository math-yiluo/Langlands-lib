# Continuity of actual adelic-level model postcomposition

`Langlands.Global.adelicLevelModelFunctoriality` proves exactly
`Langlands.Global.AdelicLevelModelFunctorialityStatement` at an arbitrary common
universe `u`. Its two clauses are:

- for arbitrary fields `k` and `F` with `Algebra k F`, every finite set `S` of
  curve places (including empty `S`), arbitrary models `X` and `Y` over
  `Spec` of `curvePlaceSIntegers k F S` and an arbitrary morphism `f : X ⟶ Y`,
  postcomposition `p ↦ p ≫ f` on `curvePlaceAdeleLevel k F S`-valued points is
  continuous for `curvePlaceLevelModelPointTopology k F S X` and
  `curvePlaceLevelModelPointTopology k F S Y`;
- for every number field `K`, every finite set `S` of finite places and
  arbitrary `f : X ⟶ Y` over `Spec` of the `S`-integers, postcomposition on
  `numberFieldAdeleLevel K S`-valued points is continuous for
  `numberFieldLevelModelPointTopology`, whose coordinates include every
  infinite factor.

No affine, finite-type, quasi-compact, quasi-separated or separated hypothesis
on `X` or `Y` is used.

## Implemented proof

Both clauses use the same argument with their own scalar rings, factors and
coordinate maps.

1. At each factor index `i`, the proof installs the `IsOpenUnits` instance from
   the published `adelicLocalFactorUnits` (first clause for curve factors,
   second for number-field factors). The factor definitions in
   `AdelicLevelModelPoints` already supply the local-ring and topological-ring
   instances, so `schemePointContinuity_proof` applies at every factor.
2. The source and target level point spaces receive their original topologies
   `curvePlaceLevelModelPointTopology` (respectively
   `numberFieldLevelModelPointTopology`), and each local base-change point space
   receives `schemePointTopology`, exactly as in the product topology
   `localModelPointProductTopology`.
3. The target coordinate map is inducing
   (`curvePlaceLevelModelPointMap_isInducing`, respectively
   `numberFieldLevelModelPointMap_isInducing`), so continuity reduces to
   continuity of the composite into the product; by `continuous_pi` it suffices
   to treat one coordinate `i`.
4. For that coordinate, `schemePointContinuity_proof` applied to the actual
   pullback `(Over.pullback (Spec.algebraMap _ _)).map f` of the model morphism
   to the factor gives a continuous map of local points. Composed with the
   continuous `i`-th source coordinate (projection after the source inducing
   map), it is continuous.
5. This composite agrees with the `i`-th target coordinate of `p ↦ p ≫ f`:
   after unfolding the coordinate map, `Category.assoc` rewrites
   `RingPoint.changeRing _ (p ≫ f)` as `RingPoint.changeRing _ p ≫ f`, and
   the published naturality `ringPointBaseChangeEquiv_natural` identifies the
   base change of this composite with the base-changed point followed by the
   pulled-back morphism. `Continuous.congr` concludes.

No bijectivity or finiteness property of the coordinate maps is used.

## Scope

This proves fixed-level functoriality only. Openness and continuity of changes
of level, model descent and independence, and the global adelic colimit remain
separate obligations of the parent program.
