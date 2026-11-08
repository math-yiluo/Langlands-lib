# Closedness of integral points over locally compact fields

Author: Worker 105.

`HenselianIntegralPointsClosedOfLocallyCompactStatement` states the closedness assertion of
Corollary 5.7 of Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed p.16, when the field is locally compact. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The module only states it and
contains no proof.

Conrad writes: "Let `X` be a (quasi-separated) algebraic space locally of finite type over the
valuation ring `R` of a field `k` equipped with a nontrivial non-archimedean absolute value, and
assume that `R` is henselian. The subset `X(R)` in `X(k)` is open and closed, and if `k` is
locally compact and `X` is of finite type over `R` then `X(R)` is quasi-compact."

## The statement

Let `K` be a nontrivially normed field that is locally compact (`LocallyCompactSpace K`), whose
closed unit ball is a subring `O` (`∀ x, x ∈ O ↔ ‖x‖ ≤ 1`). Assume `O` is a henselian local
ring. Let `X` be an algebraic space over `Spec O` that is separated (`IsSeparated X`). Let
`ι : X(O) → X_K(K)` be the map that views an `O`-point as a `K`-point
(`RingPoints.changeRing (Algebra.ofId O K)`) and then as a rational point of the base change
`baseChange (Spec.algebraMap O K) X` (`baseChangeRingPointsEquiv`). Then:

1. `ι` is injective;
2. if `X` is of finite type over `O` (`FiniteTypeOverRing O X`), the image of `ι` is closed for
   the étale-chart topology `etaleChartTopology K` of the base change.

## Relation to the source and derived content

This is the published clause `HenselianIntegralPointsClosedStatement` of
`Langlands/AlgebraicGeometry/AlgebraicSpace/HenselianIntegralPointsStatement.lean`, with the
additional hypothesis `LocallyCompactSpace K`. Its Markdown explains the corrected scope:
- "closed" needs `X` separated and of finite type;
- there are published counterexamples for quasi-separated spaces of finite type and for
  separated spaces locally of finite type.

Conrad's paper states closedness for every henselian `R`. The present special case is the one
that follows from the quasi-compactness assertion of the same corollary: a quasi-compact subset
of a Hausdorff space is closed. A locally compact field with this unit ball is complete and
non-archimedean, so `O` is automatically henselian; the hypothesis is kept as in the source. The
general henselian case remains the published statement `HenselianIntegralPointsClosedStatement`.
The name of the statement is chosen here.
