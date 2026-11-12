# Closedness of integral points over locally compact fields: proof

Authors: Worker 3519 (formerly Worker 16) and Worker 101.

Proof of `Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsClosedOfLocallyCompactStatement`
(module `HenselianIntegralPointsClosedLocallyCompactStatement`): the closedness assertion of
Corollary 5.7 of Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed pp.16–17, for a locally compact field. Registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The entry theorem is `henselianIntegralPointsClosedOfLocallyCompact`, at arbitrary universe
`u`, with exactly the hypotheses of the target: a locally compact nontrivially normed field `K`
whose closed unit ball is a henselian subring `O`, and a separated algebraic space `X` over
`Spec O`.

## Route

- **Injectivity.** The inclusion `Algebra.ofId O K` is injective. The published
  `RelativeIntegralPoints.changeRing_injective` makes change of coefficients `X(O) → X(K)`
  injective for separated `X`, and `ι` composes it with the inverse of the published
  equivalence `baseChangeRingPointsEquiv O K K X`.
- **Quasi-compact image.** A separated space is quasi-separated, since a closed immersion is
  quasi-compact. The local helper
  `HenselianIntegralPointsClosedOfLocallyCompact.isQuasiSeparated_of_isSeparated`
  reuses `HenselianFinitePointProperProof.isQuasiSeparated_of_isSeparated`.
  The published quasi-compactness part of Corollary 5.7, `henselianIntegralPointsCompact`, then
  makes the range of `ι` compact when `X` is of finite type.
- **Hausdorff target.** A locally compact nontrivially normed field is proper
  (Mathlib's `ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace`), hence
  complete, hence a henselian valued field (published `completeHenselianValuedField`). The
  generic fibre `X_K` is separated (`IsSeparated.baseChange`), quasi-separated
  (`IsQuasiSeparated.baseChange`) and locally of finite type (the finite-type atlas of `X`,
  base changed by `HasAtlasProperty.baseChange`). So its rational points are Hausdorff for the
  étale-chart topology, by the published `t2Space_etaleChartTopology` (Proposition 5.4).
- **Conclusion.** A compact subset of a Hausdorff space is closed (`IsCompact.isClosed`).

This is the route Conrad's statement suggests for locally compact fields: closedness follows
from the quasi-compactness assertion of the same corollary. The general henselian case,
`HenselianIntegralPointsClosedStatement`, is not used or proved here.

The proof uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
