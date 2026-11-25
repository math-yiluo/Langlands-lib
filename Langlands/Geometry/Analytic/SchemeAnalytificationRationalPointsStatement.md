# Statement: rational points of the glued analytification of a scheme

`SchemeAnalytificationRationalPointsStatement` is a `Prop`-valued definition in
`Langlands.Analytic.SchemeAnalytification`. It states that the actual `K`-points
of a scheme `X` locally of finite type over a complete nonarchimedean field `K`
sit inside the glued analytification `Space K f` as a topological subspace. The
statement is not proved here.

## Provenance

Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed
p.19, final paragraph of the proof of Proposition 5.11(3), says that by
[CT, Ex. 2.3.2] the analytification satisfies `X(k) = X^an(k)` as sets. Conrad
then topologizes `X(k)` through an admissible affinoid open covering of `X^an`
and states that this recovers the topology of Proposition 5.4. The registered
source is `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

Conrad–Temkin, *Non-archimedean analytification of algebraic spaces* (2009),
Example 2.3.2, printed pp.11–12, shows that analytification of closed points
gives a bijection from the closed points of `X` to the ordinary points of
`X^an`, preserving residue fields over `k`. The registered source is
`conrad-temkin-2009-nonarchimedean-analytification`, SHA256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`.

Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*
(1990), Theorem 3.4.1(i), printed p.63/PDF p.77, states for `X` locally of
finite type over `k` that `X^an(K) → X(K)` is a bijection for every
non-Archimedean field `K` over `k`. Section 3.4 assumes a nontrivial valuation.
The registered source is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.

The four clauses below are a derived formulation of these identifications for
`K`-points of schemes in the Library's Berkovich-style model. Clauses 1 and 3
concern the chosen-chart construction of `analyticRationalPoint` and have no
separate source counterpart. Clause 4 is the scheme form of Conrad's comparison
of topologies on `X(k)`. The published comparison target is the affine-chart
final topology `schemePointTopology`, not Conrad's Proposition 5.4 topology
itself. No residue-field characterization of the image is stated, since the
Library defines no residue fields for points of `Space K f`.

## Hypotheses

The statement quantifies over a nontrivially normed, ultrametric and complete
field `K` in universe `u`, a scheme `X` in the same universe, and a structure
morphism `f : X ⟶ Spec (CommRingCat.of K)` that is `LocallyOfFiniteType`. No
separatedness, quasi-compactness or nonemptiness of `X` is assumed.

## Statement

Points of `X` are the published relative points `RingPoint K (Over.mk f) K`,
and points of an affine open `U` are `RingPoint K (openOver K (Over.mk f) U) K`,
mapped to points of `X` by `openPointMap`. The four clauses are:

1. For every affine open `U` and every `K`-point `q` of `U`,
   `analyticRationalPoint K f (openPointMap K (Over.mk f) K U q)` equals
   `ι K f U (localAnalyticPoint K f U q)`. The analytic point of a `K`-point is
   therefore the same whichever affine open through the point computes it.
2. `analyticRationalPoint K f` is injective.
3. The range of `analyticRationalPoint K f` is the union over all affine opens
   `U` of the images under `ι K f U` of the range of the published affine
   analytic point map `AffineAnalytification.analyticPoint K
   (chartPresentation K f U)`.
4. `analyticRationalPoint K f` is a topological embedding when `X(K)` carries
   the published topology `schemePointTopology K (Over.mk f) K`. That topology
   is the final topology of the maps `openPointMap` from the `K`-points of all
   affine opens, each with the global-section evaluation topology.

## Expected proof route

This section is a plan, not a proof. Clause 1 needs an affine open inside the
intersection of `U` and the chosen open through the point. It also needs the
naturality of affine analytic points under restriction maps, which is stated
separately as `AffineAnalytificationRationalPointNaturalityStatement`. Clauses
2 and 3 should then follow from clause 1, from injectivity of the affine
analytic point map and from the separate gluing statement: the maps `ι K f U`
are open embeddings whose ranges meet along common affine opens. Clause 4
should combine the separate affine rational-points statement, in which the
affine analytic point map is an embedding, with the open embeddings `ι K f U`
and the open charts of `schemePointTopology`.
