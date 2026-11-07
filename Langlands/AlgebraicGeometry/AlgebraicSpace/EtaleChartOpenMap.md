# Chart maps of the étale-chart topology

Author: Worker 105.

This proof module establishes the first steps of the proof of Proposition 5.4 of Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011), printed
p.15 (registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`), for the Library's
`etaleChartTopology` (`EtaleChartTopology.lean`). It is used by
`EtaleChartTopologyFunctorial`, `EtaleChartLocalSeparation`,
`EtaleChartTopologyUniqueness` and `EtaleChartTopologyAdmissibleProof`.

Throughout, `K` is a nontrivially normed field and `X` an algebraic space over
`Spec K`. Points of schemes are `RingPoint K U K`, with `schemePointTopology K U K`;
points of spaces are `RingPoints K X K`.

## Pullbacks of presheaves

- `exists_app_of_isPullback`, `ext_app_of_isPullback`: for a pullback square of
  presheaves on schemes over a base, compatible sections over a test scheme come from a
  section of the pullback, and sections of the pullback are determined by their two
  projections. Both evaluate the square at the test scheme, where it stays a pullback
  (Mathlib's `IsPullback.map` with the evaluation functor), and use Mathlib's
  `Types.exists_of_isPullback` and `Types.ext_of_isPullback`.

## Points of maps from schemes and of their pullbacks

- `schemePointsMap a : U(K) → X(K)` is the map on rational points of a transformation
  `a : h_U → X` from the presheaf of a scheme. For a chart `c`, `c.pointMap` is
  `schemePointsMap (hom c.hom)` by definition (`EtaleFiniteTypeChart.pointMap_eq`).
- For `a : h_U → X` and `b : h_V → X`, `pairPullback a b` is the actual scheme
  representing the pullback, obtained from the representability of maps from schemes to
  `X` (`AlgebraicSpace.representable_from_scheme`). Its projections are
  `pairPullbackFst a b : U ×_X V → U` (the Yoneda preimage of the presheaf projection) and
  `pairPullbackSnd a b : U ×_X V → V`, and `pairPullback_isPullback` records the pullback
  square of presheaves.
- `etale_pairPullbackFst` and `etale_pairPullbackSnd`: the projection to `U` is étale if
  `b` is, and the projection to `V` is étale if `a` is (by the definition of `IsEtale` for
  transformations, applied to the square or its flip).
  `locallyOfFiniteType_pairPullback`: if `U` is locally of finite type over `K` and `b` is
  étale, the pullback is locally of finite type.
- `schemePointsMap_pairPullbackFst`, `exists_pairPullback_point`,
  `pairPullback_point_ext`: the rational points of `U ×_X V` are exactly the pairs
  `(x, y) ∈ U(K) × V(K)` with the same image in `X(K)`.
- `preimage_image_schemePointsMap`: for `S ⊆ U(K)`, the preimage under `b` of the image
  of `S` under `a` is the image under the second projection of the preimage of `S` under
  the first projection. This is Conrad's identity `φ⁻¹(φ'(V')) = p₁(p₂⁻¹(V'))`.

## Openness

- `isOpenMap_schemePointsMap`: if `K` is henselian, `U` is locally of finite type and
  `a` is étale, then `schemePointsMap a` is open for `etaleChartTopology K X`. By
  `etaleChartTopology_isOpen_iff` it suffices that for every chart `d` the preimage
  `d.pointMap⁻¹(a(S))` of the image of an open `S` is open. By
  `preimage_image_schemePointsMap` it is the image of an open set under the second
  projection of `U ×_X U_d`. That projection is an étale map between schemes locally of
  finite type, hence a local homeomorphism on rational points by Lemma 5.3
  (`henselianEtalePointLocalHomeomorph`, `HenselianEtalePointProof.lean`), hence open.
  The first projection is continuous by `schemePointContinuity_proof`.
- `EtaleFiniteTypeChart.isOpenMap_pointMap` is the case of a chart.

## Continuity

- `continuousAt_of_isLocalHomeomorph_comp`: if `h` is a local homeomorphism and `g ∘ h`
  is continuous at `x`, then `g` is continuous at `h x`. This follows from Mathlib's
  `IsLocalHomeomorph.map_nhds_eq`.
- `locallyOfFiniteType_of_isEtale`: if `X` is locally of finite type over its base
  (`LocallyOfFiniteTypeOverBase`, an étale surjective atlas `V → X` with `V` locally of
  finite type) and `a : h_U → X` is étale, then `U` is locally of finite type. The
  pullback of the atlas along `a` maps to `U` by an étale surjection and to `V` by an
  étale map, so it is locally of finite type. Local finite type then descends along the
  étale surjection (`locallyOfFiniteType_of_surjective_flat_locallyOfFinitePresentation_comp`).
- `exists_chart_pointMap_eq`: if `X` is quasi-separated and locally of finite type over
  `Spec K`, every point of `X(K)` is `d.pointMap y` for some chart `d`. The Library's
  proof of Knutson II.6.4 (`RationalPointEtaleLiftProof.rationalPointEtaleLiftStatement`)
  gives an étale map from an affine scheme through the point. The scheme is quasi-compact
  over `Spec K` because it is affine, and locally of finite type by
  `locallyOfFiniteType_of_isEtale`.
- `continuous_schemePointsMap`: if `K` is henselian and every point of `X(K)` lies in the
  image of a chart, then for every scheme `U` locally of finite type and every
  `a : h_U → X` (not necessarily étale), `schemePointsMap a` is continuous. At a point `x`,
  choose a chart `d` through the image of `x` and a point `w` of `U ×_X U_d` over `x`. The
  first projection `U ×_X U_d → U` is étale, so a local homeomorphism on rational points by
  Lemma 5.3, and `schemePointsMap a ∘ fst = d.pointMap ∘ snd` is continuous. So
  `schemePointsMap a` is continuous at `x` by `continuousAt_of_isLocalHomeomorph_comp`.
