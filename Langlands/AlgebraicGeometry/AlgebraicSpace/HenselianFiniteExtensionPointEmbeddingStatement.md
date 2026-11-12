# Rational points over a finite extension of henselian valued fields

Author: Worker 3519.

`HenselianFiniteExtensionPointEmbeddingStatement` states the finite-degree supplement in the
proof of Proposition 5.11(3) of Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011), registered as `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The module
contains one Prop-valued statement and no proof.

## Source

Proposition 5.11 (printed p.18) begins: "Let `k′/k` be an extension of henselian valued
fields, and `X` a (quasi-separated) algebraic space locally of finite type over `k`." Part (3)
assumes that `X` is covered by separated Zariski-open subsets. In the finite-degree part of
the proof (printed p.19), Conrad shows that the canonical map `j : X → Res_{k′/k}(X_{k′})` is a
closed immersion when `X` is separated, and adds in parentheses: "If `Δ_{Y′/k′}` is a
quasi-compact immersion, so the same holds for `Δ_{Res_{k′/k}(Y′)/k} = Res_{k′/k}(Δ_{Y′/k′})`,
then any section to `π` is quasi-compact. Hence, even without completeness, `X(k) → X(k′)` is
a topological embedding whenever `[k′ : k]` is finite and `Δ_{X/k}` is a quasi-compact
immersion."

## Statement

For fields `K` and `K'` in one universe `u`:

- `K` and `K'` are nontrivially normed fields with `NormedAlgebra K K'`, so the norm of `K'`
  restricts to that of `K`, and `K'` is finite-dimensional over `K`;
- both are henselian valued fields (`IsHenselianValuedField`: the norm extends uniquely to
  every algebraic extension field, Conrad's definition on printed p.14);
- `X` is an algebraic space over `Spec K` with `IsLocallySeparatedLocallyFiniteType K X`:
  quasi-separated, locally of finite type, and locally separated, that is, its diagonal is an
  immersion (`IsLocallySeparated`, from `HenselianSpacePointTopologyStatement`).
  Quasi-separatedness makes the diagonal quasi-compact, so together these say exactly that
  `Δ_{X/K}` is a quasi-compact immersion.

The conclusion is that `φ : X(K) → X_{K'}(K')` is a topological embedding. Here `φ` sends a
rational point to the `K'`-valued point obtained by changing the value ring along `K → K'`,
then to the corresponding rational point of the base change
`baseChange (Spec.algebraMap K K') X`, through `baseChangeRingPointsEquiv`. This is the same
map as in `HenselianExtensionPointEmbeddingStatement`. Both point sets carry the étale-chart
topologies `etaleChartTopology K X` and `etaleChartTopology K' (baseChange … X)`, the topology
of Conrad's proof of Proposition 5.4.

No completeness of `K` or `K'` is assumed, and `X` need not be covered by separated open
subspaces.

## Relation to other statements

`HenselianExtensionPointEmbeddingStatement` states Proposition 5.11(3) for extensions of any
degree, under the hypothesis `IsCoveredBySeparatedOpenSubspaces`. A space covered by separated
open subspaces `U_i` has an immersive diagonal: it is a closed immersion into the open union of
the `U_i × U_i`. So for finite extensions the embedding clause of that statement follows
mathematically from the present one; no Lean bridge between them is stated. The present statement does not assert the
closed-embedding clause of part (3). Example 5.13 (`HenselianExtensionPointNotClosedStatement`)
shows that closedness can fail under the present hypotheses.

## Provenance

The assertion is Conrad's. The derived choices are the encoding of "`Δ_{X/k}` is a
quasi-compact immersion" as quasi-separated and locally separated, and the use of the
Library's étale-chart topology and point maps. Conrad's proof route is through
Proposition 5.11(1) for `Y′ = X_{K'}` and the section `j` of `π`; the corrected
Proposition 5.4 (`HenselianSpacePointTopologyStatement`) applies to quasi-separated, locally
separated spaces locally of finite type, which is the scope assumed here.
