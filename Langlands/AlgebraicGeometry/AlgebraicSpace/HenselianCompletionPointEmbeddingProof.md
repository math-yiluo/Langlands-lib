# Rational points over a henselian field embed into points over its completion

Author: Worker 105.

This module proves `HenselianCompletionPointEmbeddingStatement`
(`HenselianCompletionPointEmbeddingStatement.lean`), part (2) of Proposition 5.11 of
Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011),
printed p.18 (registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`). The entry theorem
is `henselianCompletionPointEmbedding : HenselianCompletionPointEmbeddingStatement.{u}`.
It depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

Throughout, `K` is a nontrivially normed field, `K̂ = UniformSpace.Completion K`, and
`X` an algebraic space over `Spec K`. Points of schemes are `RingPoint K U K` with
`schemePointTopology K U K`; points of spaces are `RingPoints K X K` with
`etaleChartTopology K X`. The same notation is used over `K̂`, which is a nontrivially
normed complete field (`completionNontriviallyNormedField`,
`HenselianEtalePointProof.lean`).

## Route

Conrad's proof (printed p.19) chooses an étale cover `U → X` by a separated scheme with
`U(k) → X(k)` surjective, and uses that the points of `U_{k̂}` over rational points of
`X` are rational because `k` is henselian. The Lean proof follows this idea, but works
with all étale charts of finite type at once (the charts defining
`etaleChartTopology`), and it needs neither a single cover nor any separatedness. It
also does not use the existence part of Proposition 5.4 for `X`; it uses only the
definition of the étale-chart topology over `K` and over `K̂`.

## Openness of chart maps over a complete field

- `isOpenMap_schemePointsMap_of_etaleOpen`: suppose that every étale morphism of
  schemes locally of finite type over `K` is open on rational points. Then for every
  scheme `U` locally of finite type and every étale `a : h_U → X`, the map
  `schemePointsMap a : U(K) → X(K)` is open for `etaleChartTopology K X`. The proof is
  that of `isOpenMap_schemePointsMap` (`EtaleChartOpenMap.lean`) with this hypothesis in
  place of Lemma 5.3: for a chart `d`, the preimage under `d.pointMap` of the image of
  an open set is the image under the étale second projection of `U ×_X U_d` of an open
  set (`preimage_image_schemePointsMap`).
- `isOpenMap_schemePointsMap_of_complete`: if `K` is complete, the hypothesis holds by
  the Library's `isOpenMap_smoothSchemePointMap` (`CompleteFieldSmoothOpenProof.lean`),
  since étale morphisms are smooth. No henselian hypothesis is needed here.

## Base change of charts and of points

- `EtaleFiniteTypeChart.completion c` is the base change of a chart `c : U → X` to `K̂`:
  the scheme `ringBaseChange K K̂ U` (the actual pullback `U ×_K Spec K̂`) with the map
  `restrictAtlas` to `X_{K̂}` from `SpaceBaseChange.lean`. It is étale by
  `relative_restrictAtlas`, and locally of finite type and quasi-compact over `K̂` by
  base change of these properties.
- `baseChangeRingPointsEquiv_completion_pointMap`: under
  `baseChangeRingPointsEquiv K K̂ K̂ X : X_{K̂}(K̂) ≃ X(K̂)`, the chart map of the
  base-changed chart sends a point `p` to the image under `c.hom` of the point of `U`
  corresponding to `p` under `ringPointBaseChangeEquiv`.
- `completionSchemePointMap U : U(K) → U_{K̂}(K̂)` is the coefficient change along
  `K → K̂` followed by `ringPointBaseChangeEquiv`. It is a topological embedding
  (`isEmbedding_completionSchemePointMap`): the coefficient change is an embedding by
  the Library's `isEmbedding_schemeChangeRing` (`HenselianEtalePointProof.lean`), since
  `K → K̂` is a uniform embedding, and `ringPointBaseChangeEquiv` is a homeomorphism by
  `schemeBaseChangeTopology_proof` (`SchemeBaseChangeTopologyProofs.lean`).
- `completionPointMap X : X(K) → X_{K̂}(K̂)` is the map of the statement, and
  `completionPointMap_pointMap` says that it commutes with chart maps:
  `completionPointMap X (c.pointMap u) = c.completion.pointMap (completionSchemePointMap u)`.
  This follows from `RingPoints.changeRing_map`.

## Rationality

`exists_rational_of_completion`: let `K` be henselian, `a : h_U → X` étale,
`b : h_V → X` arbitrary, `η ∈ U(K̂)` and `v ∈ V(K)` with the same image in `X(K̂)`.
Then `η` is the image of some `u ∈ U(K)` with `a(u) = b(v)` in `X(K)`. The pair
`(η, v)` gives a `K̂`-point `w` of `W = U ×_X V` (`exists_app_of_isPullback`). The
projection `W → V` is étale (`etale_pairPullbackSnd`), hence formally unramified, and
`w` lies over the rational point `v`. Since `K` is separably closed in `K̂`
(`separableClosure_completion_eq_bot`, using that `K` is henselian), the Library's
`exists_changeRing_eq_of_formallyUnramified` shows that `w` is rational. Its first
projection is the required `u`.

## The embedding

`henselianCompletionPointEmbedding`: let `K` be henselian and `X` quasi-separated and
locally of finite type over `Spec K`. Every point of `X(K)` lies in the image of some
chart (`exists_chart_pointMap_eq`, `EtaleChartOpenMap.lean`).

- Rational points over a point: if `c.completion.pointMap η = completionPointMap X y`,
  then `η = completionSchemePointMap u` for some `u ∈ U_c(K)` with `c.pointMap u = y`.
  Write `y = d.pointMap v` for a chart `d` and apply `exists_rational_of_completion` to
  `c` and `d`.
- Injectivity: write `x = c.pointMap u`; if `x` and `y` have the same image, the
  previous step gives `u'` with `completionSchemePointMap u' = completionSchemePointMap u`
  and `c.pointMap u' = y`, so `u' = u` and `x = y`.
- Continuity: by `etaleChartTopology_continuous_iff` it suffices that each composite
  `completionPointMap X ∘ c.pointMap = c.completion.pointMap ∘ completionSchemePointMap`
  is continuous, which holds by `EtaleFiniteTypeChart.continuous_pointMap` and the
  scheme embedding.
- Inducing: let `W ⊆ X(K)` be open. For each chart `c`, `c.pointMap⁻¹(W)` is open, so
  equals `completionSchemePointMap⁻¹(t_c)` for an open `t_c ⊆ U_c,K̂(K̂)`. The set
  `T = ⋃_c c.completion.pointMap(t_c)` is open in `X_{K̂}(K̂)` because base-changed
  chart maps are open over the complete field `K̂`, and the two previous facts give
  `completionPointMap X⁻¹(T) = W`.

Hence `completionPointMap X` is a topological embedding.
