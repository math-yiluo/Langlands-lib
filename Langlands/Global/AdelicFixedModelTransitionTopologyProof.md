# Topology of actual fixed-base arithmetic coefficient changes

`Langlands.Global.adelicFixedModelTransitionTopology` proves exactly
`Langlands.Global.AdelicFixedModelTransitionTopologyStatement` at an arbitrary
common universe `u`. It is the pair of
`curvePlaceFixedModelTransitionTopology` (proving
`CurvePlaceFixedModelTransitionTopologyStatement`) and
`numberFieldFixedModelTransitionTopology` (proving
`NumberFieldFixedModelTransitionTopologyStatement`).

For a model `X` over `Spec` of the original outside-`S` integer ring with
`LocallyOfFiniteType X.hom` and `QuasiCompact X.hom`, and finite superlevels
`T ≤ U` of `S`, each clause shows that the literal fixed-base coefficient map
`RingPoint.changeRing (…AdeleLevelOverMap … S hTU).hom (X := X)` is continuous
and open for the transported stage topologies
`curvePlaceFixedModelStageTopology` (respectively
`numberFieldFixedModelStageTopology`) at `T` and `U`, and is an open embedding
under `IsSeparated X.hom`. The hypotheses are exactly those of the target: the
curve clause has arbitrary fields `k`, `F` with `Algebra k F`, the
`Algebra (RatFunc k) F` presentation, the scalar tower and `FunctionField k F`;
the number-field clause has an arbitrary number field `K`, whose level rings
contain every infinite factor. Every finite `S`, including empty `S`, and
arbitrary nonaffine `X` are allowed. Separatedness is used only for the
open-embedding conjunct.

## Implemented proof

1. **Isomorphism homeomorphisms.** For an actual isomorphism `e : X ≅ Y` of
   models at one level, `curvePlaceLevelModelIsoHomeomorph` and
   `numberFieldLevelModelIsoHomeomorph` build a homeomorphism of stage points
   for `curvePlaceLevelModelPointTopology` (respectively
   `numberFieldLevelModelPointTopology`) with forward map `p ↦ p ≫ e.hom` and
   inverse `p ↦ p ≫ e.inv`. The inverse identities follow from
   `Category.assoc`, `e.hom_inv_id`, `e.inv_hom_id` and `Category.comp_id`;
   both directions are continuous by the corresponding clause of the published
   `adelicLevelModelFunctoriality`.
2. **Finite type of the pulled-back model.** Write `XT` for the actual pullback
   `…LevelModelBaseChange … T.property X`. Unfolding this definition,
   instance search gives `LocallyOfFiniteType XT.hom` and `QuasiCompact XT.hom`
   (and, in the separated case, `IsSeparated XT.hom`) by stability of these
   properties under pullback.
3. **Original changing-level transition.** The published
   `adelicLevelModelTransitionTopology` (first clause for curves, second for
   number fields), applied to `T.val ⊆ U.val` and `XT`, shows that
   `…LevelModelTransition … hTU XT` is continuous and open, and an open
   embedding when `XT` is separated.
4. **Composite.** Let `source` be `…FixedModelPointHomeomorph … X T` and
   `target` the composite of the isomorphism homeomorphism for the canonical
   comparison `…FixedModelPullbackCompIso … X hTU` (twice-pulled to directly
   pulled model at `U`) with the inverse of `…FixedModelPointHomeomorph … X U`.
   The published naturality theorem `curvePlaceFixedModelTransition_natural`
   (respectively `numberFieldFixedModelTransition_natural`) gives, pointwise,
   `target (transition (source p)) = RingPoint.changeRing … p`, so by function
   extensionality the composite equals the literal fixed-base coefficient map.
5. **Transfer.** Continuity and openness of the composite follow from
   `Continuous.comp` and `IsOpenMap.comp` with the homeomorphisms; under
   `IsSeparated X.hom`, `IsOpenEmbedding.comp` with
   `Homeomorph.isOpenEmbedding` gives the open embedding. Rewriting by the
   identity of step 4 yields the three conjuncts.

The compiled theorem uses only `propext`, `Classical.choice` and
`Quot.sound`.
