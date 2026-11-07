# Separated spaces: Hausdorff and locally compact rational points

Author: Worker 105.

This proof module proves two of the three separated-space properties of Proposition 5.4
of Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011),
printed p.15 (source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`): "If `X` is separated
then the topology on `X(k)` is Hausdorff, and it is ... locally compact when `k` is ...
locally compact." The third property, total disconnectedness over non-archimedean `k`,
is proved in `EtaleChartTotallyDisconnected`. This module builds on
`EtaleChartLocalSeparation`.

- `isClosedEmbedding_pairPullback_points`: if `X` is separated (the diagonal is a
  representable closed immersion, `IsSeparated`), then for maps `a : h_U → X`,
  `b : h_V → X` from schemes the rational points of `U ×_X V` form a closed subspace of
  `U(K) × V(K)`. The pairing `U ×_X V → U ⊗ V` is a closed immersion
  (`isClosedImmersion_pairPullbackLift`). Closed immersions give closed embeddings on
  points over the Hausdorff field `K` (`isClosedEmbedding_schemeClosedPointMap`). The
  Library's `schemeProductPointHomeomorph` identifies `(U ⊗ V)(K)` with `U(K) × V(K)`.
- `t2Space_etaleChartTopology` (Hausdorff): over a henselian valued field, if `X` is
  quasi-separated, locally of finite type and separated, then `X(K)` is Hausdorff. Let
  `x ≠ y` be the images of `u ∈ U_c(K)` and `v ∈ U_d(K)` under charts `c`, `d`. The pair
  `(u, v)` lies outside the closed set of pairs with equal images. A product neighbourhood
  `N × M` of `(u, v)` avoids that set, so the open sets `c(N)` and `d(M)` (chart maps are
  open) are disjoint neighbourhoods of `x` and `y`. Conrad derives the property formally
  from closed immersions and fibre products; the proof here uses the chart overlaps
  directly.
- `locallyCompactSpace_etaleChartTopology` (locally compact): over a locally compact
  henselian valued field, `X(K)` is locally compact for every quasi-separated `X` locally
  of finite type (separatedness is not needed). Given a neighbourhood `n` of `x = c(u)`,
  the Library's local compactness of scheme points
  (`schemePointLocalCompactness_proof`) gives a compact neighbourhood `s` of `u` inside
  the preimage of `n`. Its image `c(s)` is compact and is a neighbourhood of `x`, because
  the chart map is open.
