# Open immersions on actual arithmetic-level model points: proof

Authors: Worker 3519 (formerly Worker 16), Worker 128.

Worker 3519 supplied the complete proof draft for Task 5275; Worker 128
checked the dependencies and source correspondence, prepared the proof for
submission, and clarified this documentation.

`Langlands.Global.adelicLevelModelOpenImmersion` proves exactly
`AdelicLevelModelOpenImmersionStatement` in its original universe. Both
arithmetic clauses keep the original scheme models, scalar actions, coefficient
rings and level point topologies, including all infinite number-field factors
and arbitrary constant fields in the curve clause. Each finite set `S` may be
empty. Neither affine nor separated models are required.

## Embedding part

`curvePlaceLevelModelPointMap_isEmbedding_of_isOpenImmersion` and
`numberFieldLevelModelPointMap_isEmbedding_of_isOpenImmersion` treat an open
immersion `f : X ⟶ Y` of models over the `S`-integers.

1. **Local factors.** `localModelPointMap_isOpenEmbedding` base changes `f` to a
   local factor `R`. Open immersions are stable under pullback
   (`MorphismProperty.overPullbackMap`), and the Library's
   `isOpenEmbedding_schemePointMap` makes postcomposition an open embedding on
   the actual local point spaces. It needs `R` to be a local topological ring
   with open units and continuous inversion. The level factors carry
   `IsTopologicalRing` and `IsLocalRing` instances, and `adelicLocalFactorUnits`
   supplies `IsOpenUnits`.
2. **Product.** Each open embedding is an embedding, and an arbitrary product of
   embeddings is an embedding (`IsEmbedding.piMap`). The product of the open
   embeddings need not be open, which is the point of the statement.
3. **Commuting square.** `localModelPointMap_natural` is naturality of
   coefficient restriction and actual scheme base change. It shows that the level
   point map of `Y` after postcomposition with `f` equals the product of the local
   postcompositions after the level point map of `X`.
4. **Inducing.** The level topologies are by definition induced by the level
   point maps (`curvePlaceLevelModelPointMap_isInducing`,
   `numberFieldLevelModelPointMap_isInducing`). So the composite in step 3 is
   inducing. Continuity of postcomposition follows from inducing of the target
   level map, and `IsInducing.of_comp` cancels it.
5. **Injective.** `postcomp_injective`: an open immersion is a monomorphism of
   schemes, so `p.left ≫ f.left = q.left ≫ f.left` forces `p = q`.

This part uses neither finite type nor any homeomorphism onto the product, so
the finite-type assumptions of the statement are not used.

## Non-openness part

`curvePlaceLevel_puncture_not_isOpen` and `numberFieldLevel_puncture_not_isOpen`.
The affine line over the `S`-integers is affine, so
`curvePlaceLevelModelPointTopology_eq_affine` and
`numberFieldLevelModelPointTopology_eq_affine` replace the level topology by the
ordinary evaluation topology with values in the level ring. The Library lemma
`affineLineUnitLocusObstruction_of_nonunit_tendsto` then shows that the image of
the punctured line is not open, once a sequence of nonunits of the level ring
converging to `1` is supplied.

That sequence is `curvePlaceLevelNonunitSequence` (respectively
`numberFieldLevelNonunitSequence`). It is the Library's adelic sequence
`curvePlaceNonunitSequence` (respectively `numberFieldNonunitSequence`), whose
`n`-th term has finite coordinate `0` at the `n`-th of a sequence of distinct
places and `1` elsewhere. All its coordinates are `0` or `1`, so it lies in the
level ring for every `S`. It converges to `1` in the adele ring, hence in the
level subring with its subspace topology (`tendsto_subtype_rng`). A unit of the
level ring would be a unit of the adele ring, which the Library excludes. The
curve sequence uses `functionField_places_infinite`, valid for an arbitrary
constant field.

## Source

Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), paragraph after the proof of Theorem 3.6, printed pp.8–9. Registered
source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. Conrad's
reason, "an arbitrary product of open embeddings is a topological embedding but
usually does not have open image", is the route of the embedding part.
