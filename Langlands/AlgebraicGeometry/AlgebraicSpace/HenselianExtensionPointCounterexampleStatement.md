# The closed-embedding property fails without separated open covers

Author: Worker 105.

`HenselianExtensionPointNotClosedStatement` states the counterexample of Example 5.13 in Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011), printed p.20.
The registered source is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. The module only states it
and contains no proof.

Conrad writes on printed p.20: "We now show if the hypothesis on `X` in Proposition 5.11(3)
(which is always satisfied in the scheme case) is weakened to the condition that the
quasi-compact `Δ_{X/k}` is an immersion, then the closed embedding property for
`X(k) → X(k′)` can fail even when `k` is complete with respect to a nontrivial discrete
valuation and `k′/k` is finite separable." He then takes a separable quadratic extension
`k′/k`, with `k` complete for a nontrivial non-archimedean absolute value. `X` is the
quotient of the affine `k′`-line by the free action of the étale group obtained from
`(Z/2Z)_L` by deleting the non-identity point over the origin of the affine line `L` over
`k`. Its diagonal is "a quasi-compact immersion (even affine)". `X(k)` is homeomorphic to
`k^×`, `X_{k′}` is the affine `k′`-line with a doubled origin, and the map
`X(k) → X(k′)` "has non-closed image".

## The statement

Let `K` be a nontrivially normed field that is complete (`CompleteSpace K`) with an
ultrametric absolute value (`IsUltrametricDist K`), and `K'` a normed `K`-algebra field with
`Module.finrank K K' = 2` and `Algebra.IsSeparable K K'`. Then there is an algebraic space `X`
over `Spec K` such that:

1. `X` is quasi-separated and locally of finite type over `K`
   (`IsQuasiSeparatedLocallyFiniteType K X`, from
   `Langlands/AlgebraicGeometry/AlgebraicSpace/HenselianSpacePointTopologyStatement.lean`);
2. the diagonal `diag X.presheaf` is representable, and every represented projection is an
   immersion of schemes and an affine morphism;
3. the image of the map `X(K) → X_{K'}(K')` is not closed for the étale-chart topology
   `etaleChartTopology K'` of the base change `baseChange (Spec.algebraMap K K') X`.

The map in (3) is the one of the published Proposition 5.11(3) statement
(`HenselianExtensionPointEmbeddingStatement`): view a rational point as a `K'`-valued point
(`RingPoints.changeRing (Algebra.ofId K K')`), then as a rational point of the base change
(`baseChangeRingPointsEquiv`).

## Relation to the source and derived content

The statement asserts the existence of Conrad's space with the properties he uses. Conrad
also states that his `X` is smooth and irreducible, that `X(K) → K` is a homeomorphism onto
`K^×`, and that `X_{K'}` is the affine line with a doubled origin. These are part of his
verification and are not stated here; the construction itself is not formalized here.

Since `K'` is finite over the complete field `K`, `K` is closed in `K'`. So (3) shows that the
closed-embedding conclusion of Proposition 5.11(3) fails when the hypothesis
`IsCoveredBySeparatedOpenSubspaces` is replaced by the diagonal condition (2). Complete
valued fields are henselian, so the étale-chart topologies are the topologies of Conrad's
Proposition 5.4 (published `EtaleChartTopologyAdmissibleStatement`).

Conrad's first sentence mentions a nontrivial discrete valuation; his construction works for
any complete nontrivial non-archimedean absolute value, which is the generality stated here.
Separable quadratic extensions are formalized as `Module.finrank K K' = 2` with
`Algebra.IsSeparable K K'`. The name of the statement is chosen here.
