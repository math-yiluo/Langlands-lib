# Proof that rational points of locally separated spaces are locally Hausdorff

Author: Worker 67.

This module proves `LocallySeparatedRationalPointsStatement` for an arbitrary universe `u`.
The entry theorem is `locallySeparatedRationalPoints`. The statement is the corrected
topological claim of Conrad's Example 5.5 (Brian Conrad, *Weil and Grothendieck approaches
to adelic points*, December 31, 2011, printed p.16; registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`) for an arbitrary
quasi-separated, locally separated algebraic space locally of finite type. Its meaning and
the correction are explained in `LocallySeparatedRationalPointsStatement.md`. Conrad gives
no argument for this claim. The proof follows the derivation sketched in that Markdown.

## Two facts on affine charts

Let `U` be a `K`-scheme with `IsAffine U.left`, and give `U(K)` the scheme point topology
`schemePointTopology K U K`.

- `t2Space_schemePointTopology_of_isAffine`: `U(K)` is Hausdorff. By
  `schemePointTopology_eq_affine`, the scheme point topology of an affine scheme is the
  evaluation topology. The homeomorphism `affineSchemePointHomeomorph` identifies `U(K)`
  with `AlgPoint K Γ(U) K`, the `K`-algebra maps `Γ(U) → K`. This space carries the
  topology induced from the product `Γ(U) → K`, and it is Hausdorff because `K` is
  (the `T2Space` instance in `PointTopology/Affine.lean`).
- `totallyDisconnectedSpace_schemePointTopology_of_isAffine`: if the norm of `K` is
  ultrametric (`IsUltrametricDist K`), then `U(K)` is totally disconnected. Mathlib's
  instance in `Mathlib.Topology.MetricSpace.Ultra.TotallySeparated` makes `K` totally
  separated, hence totally disconnected. So the product `Γ(U) → K` is totally disconnected.
  `AlgPoint.isEmbedding_evaluation` embeds `AlgPoint K Γ(U) K` into this product, so
  `AlgPoint K Γ(U) K` is totally disconnected (Mathlib's
  `IsEmbedding.isTotallyDisconnected_range`). The homeomorphism transports this to `U(K)`.

These facts use only that `U(K)` embeds into a power of `K`, indexed by all global sections
of `U`. The Lean proof does not use that `U(K)` is closed or that finitely many coordinates
suffice.

## The main proof

Let `K` be a nontrivially normed field with `hK : IsHenselianValuedField K`. Let `X` be an
algebraic space over `Spec K` with `hX : IsLocallySeparatedLocallyFiniteType K X`. Give
`X(K)` the topology `etaleChartTopology K X`, and let `x` be a rational point.

1. **Affine chart.** The Library's `exists_affine_chart_pointMap_eq`
   (`EtaleChartTotallyDisconnected.lean`) gives an étale chart of finite type
   `c : EtaleFiniteTypeChart K X` with an affine chart scheme `U` and a rational point `u`
   of `U` with `c.pointMap u = x`. It uses that `X` is quasi-separated and locally of
   finite type over `K`.
2. **Local injectivity.** `X` is locally separated, and the chart map is étale. So the
   Library's `exists_isOpen_injOn_schemePointsMap` (`EtaleChartLocalSeparation.lean`)
   gives an open set `N ∋ u` of `U(K)` on which the map of rational points is injective.
   This map agrees definitionally with `c.pointMap`.
3. **Open embedding.** Let `g : N → X(K)` be the restriction of `c.pointMap`. It is
   continuous (`EtaleFiniteTypeChart.continuous_pointMap`) and injective (step 2). It is
   open, because `c.pointMap` is an open map over a henselian field
   (`EtaleFiniteTypeChart.isOpenMap_pointMap`, `EtaleChartOpenMap.lean`) and `N` is open.
   So `g` is an open embedding (Mathlib's
   `IsOpenEmbedding.of_continuous_injective_isOpenMap`).
4. **The neighbourhood.** Let `W` be the range of `g`. It is open in `X(K)` and contains
   `g u = x`. The embedding gives a homeomorphism `e : N ≃ₜ W`
   (`IsEmbedding.toHomeomorph`).
5. **Hausdorff.** `N` is a subspace of `U(K)`, which is Hausdorff by
   `t2Space_schemePointTopology_of_isAffine`. So `W` is Hausdorff, since `e.symm` embeds it
   into `N`.
6. **Locally compact.** Assume `K` is locally compact. Then `X(K)` is locally compact by
   the Library's `locallyCompactSpace_etaleChartTopology` (`EtaleChartSeparated.lean`),
   which needs only that `X` is quasi-separated and locally of finite type. So the open
   subset `W` is locally compact (Mathlib's `IsOpen.locallyCompactSpace`).
7. **Totally disconnected.** Assume the norm of `K` is ultrametric. Then `U(K)` is totally
   disconnected by `totallyDisconnectedSpace_schemePointTopology_of_isAffine`, so is its
   subspace `N`, and so is `W` via `e`.

Local separatedness is used only in step 2. The henselian hypothesis is used only in
steps 3 and 6.

## Scope

The module adds the two affine-chart theorems above and the entry theorem. It does not
change the statement module or any other Library file. `lean_check` reports the axioms
`propext`, `Classical.choice` and `Quot.sound`.
