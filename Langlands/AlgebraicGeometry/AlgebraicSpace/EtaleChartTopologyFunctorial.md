# Functoriality and immersions for the étale-chart topology

Author: Worker 105.

This proof module proves four of the six properties of the corrected Proposition 5.4 of
Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011),
printed pp.14–16 (source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`) for the étale-chart
topology. These are functoriality, the scheme case, open immersions and closed immersions.
It also proves that étale morphisms induce open maps. The hypotheses used are only
quasi-separatedness and local finite type (`IsQuasiSeparatedLocallyFiniteType`, from
`HenselianSpacePointTopologyStatement.lean`). Local separatedness is not needed here. It
builds on `EtaleChartOpenMap`.

Throughout, `K` is a nontrivially normed field with `IsHenselianValuedField K` where
stated, and rational points of spaces carry `etaleChartTopology`.

## Results

- `IsQuasiSeparatedLocallyFiniteType.exists_chart`: rational points of such spaces are
  covered by chart images (`exists_chart_pointMap_eq`).
- `continuous_ringPointsMap` (functoriality): for `f : X ⟶ Y` with `Y` quasi-separated
  and locally of finite type, `RingPoints.map f` is continuous. By
  `etaleChartTopology_continuous_iff` it suffices that `RingPoints.map f ∘ c.pointMap`
  is continuous for each chart `c` of `X`. This composite is
  `schemePointsMap (hom c.hom ≫ hom f)`, continuous by `continuous_schemePointsMap`.
- `isHomeomorph_schemeRingPointsEquiv` (the case of schemes): for a scheme `U` whose
  space is quasi-separated and locally of finite type, the identification
  `schemeRingPointsEquiv K U K` of the points of the space with the scheme points is a
  homeomorphism from the étale-chart topology to `schemePointTopology`.
  - Continuity: the map of each chart is a scheme morphism (the Yoneda preimage of the
    chart transformation), so the composite with a chart map is postcomposition with an
    actual scheme morphism, continuous by `schemePointContinuity_proof`.
  - Continuity of the inverse: the inverse is `schemePointsMap` of the identity of `h_U`,
    continuous by `continuous_schemePointsMap`. `U` is locally of finite type by
    `locallyOfFiniteTypeOverBase_schemeToSpace_iff`.
- `map_schemePointsMap_fst`, `exists_pullback_point`, `preimage_image_ringPointsMap`: for
  a morphism `f : X' ⟶ X` with representable underlying transformation and a map
  `a : h_U → X`, the rational points of the represented pullback are the pairs
  `(x', y) ∈ X'(K) × U(K)` with the same image in `X(K)`, and preimages of images
  transform as in `EtaleChartOpenMap`.
- `injective_ringPointsMap_of_mono`: if every represented projection of `hom f` is a
  monomorphism, `RingPoints.map f` is injective. Two points with the same image both
  lift to sections of the projection of the pullback along that common image (a map from
  `Spec K`). The two sections agree because the projection is a monomorphism.
- `etaleChartTopology_isClosed_iff`: a set is closed exactly when all its chart preimages
  are closed.
- `isOpenEmbedding_ringPointsMap` (open immersions): if `hom f` is a representable open
  immersion (the Library's `IsOpenImmersion` for transformations) and `X'`, `X` are
  quasi-separated and locally of finite type, then `RingPoints.map f` is an open
  embedding. It is continuous by functoriality and injective because open immersions are
  monomorphisms. For openness, the preimage in a chart `c` of the image of an open
  `O ⊆ X'(K)` is, by `preimage_image_ringPointsMap`, the image under the open immersion
  `U_c ×_X X' → U_c` of the preimage of `O`. That preimage is open by
  `continuous_schemePointsMap`. Its image is open by `isOpenEmbedding_schemePointMap`
  (open immersions of schemes give open embeddings on points).
- `isClosedEmbedding_ringPointsMap` (closed immersions): the same argument with closed
  sets and `isClosedEmbedding_schemeClosedPointMap` (closed immersions of schemes give
  closed embeddings on points over the Hausdorff field `K`).
- `isOpenMap_ringPointsMap_of_isEtaleMorphism`: if `f` is étale in the Stacks sense
  (`IsEtaleMorphism`, Tag 03FR) and `X'` is quasi-separated and locally of finite type,
  then `RingPoints.map f` is open. The image of an open `O` is the union over the charts
  `c` of `X'` of the images of `c.pointMap⁻¹(O)` under `schemePointsMap (hom c.hom ≫ hom f)`.
  These maps are étale, hence open by `isOpenMap_schemePointsMap`.

Conrad derives the open and closed immersion cases from compatibility with fibre
products. The proof here argues directly with charts and does not use fibre products.
