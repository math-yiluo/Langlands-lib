# Rational points of the glued analytification of a scheme

This module defines the map from the actual `K`-points of a scheme `X` locally of
finite type over a complete nonarchimedean field `K` to the glued analytification
`Space K f` of `SchemeAnalytificationSpace`. A `K`-point factors through some
affine open `U` of `X`. The module sends it to the analytic point, in the
polynomial-locus analytification of `U`, of the corresponding `K`-algebra map
on global sections. It then sends that point into the glued space. The module
also supplies the algebraic bridge between the two published notions of the
coordinate algebra of an affine scheme over `Spec K`. It proves no property of
the map beyond its definition. Independence of the chosen affine open,
injectivity and the comparison of topologies are stated in
`SchemeAnalytificationRationalPointsStatement` and proved as
`schemeAnalytificationRationalPoints` in `SchemeAnalytificationRationalPointsProof`.

## Provenance

Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed
p.19, final paragraph of the proof of Proposition 5.11(3), says that the
analytification `X^an` of [CT] satisfies `X(k) = X^an(k)` as sets, citing
[CT, Ex. 2.3.2]. Conrad uses this identification to topologize `X(k)` through
an admissible affinoid covering of `X^an`. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

Conrad–Temkin, *Non-archimedean analytification of algebraic spaces* (2009),
Example 2.3.2, printed pp.11–12, defines for an analytifiable algebraic space a
map from the closed points of `X` to the points of `X^an` by analytifying the
closed point `Spec(k') → X`, and states that it is bijective and preserves
residue fields over `k`. Restricted to residue field `k`, this is the
identification `X(k) = X^an(k)`. The registered source is
`conrad-temkin-2009-nonarchimedean-analytification`, SHA256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`.

Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*
(1990), Theorem 3.4.1(i), printed p.63/PDF p.77, states for a scheme `X`
locally of finite type over `k` that `X^an(K) → X(K)` is a bijection for every
non-Archimedean field `K` over `k`. Section 3.4 assumes a nontrivial valuation,
as `NontriviallyNormedField` does here. The registered source is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.

The map below is a derived implementation of the direction `X(K) → X^an` of
these identifications in the Library's Berkovich-style polynomial-locus model.
It goes through a chosen affine open, which no source uses. The bridge
`coordinateAlgEquiv` is internal: it reconciles two Library conventions and has
no source counterpart.

## Hypotheses

All declarations lie in `Langlands.Analytic.SchemeAnalytification`. In the
algebraic section `K` is any commutative ring and `Y` is a scheme in the
universe `u` of `K`. In the section on points `K` is a nontrivially normed,
ultrametric and complete field. `f : X ⟶ Spec (CommRingCat.of K)` is the
structure morphism and is `LocallyOfFiniteType`. No separatedness,
quasi-compactness or nonemptiness of `X` is assumed.

## The coordinate-algebra bridge

For an affine scheme `Y` and `g : Y ⟶ Spec (CommRingCat.of K)`, the instance
`isAffine_overMk_left` records that the underlying scheme of `Over.mk g` is
affine; it is `Y` itself.

Two published types carry the global sections `Γ(Y, ⊤)` of `Y` with a
`K`-algebra structure. `CoordinateRing g` of `AffineSchemeAnalytification` takes
the structure from the global-section map `g.appTop`.
`AffineCoordinateRing K (Over.mk g)` of the point-topology Library takes it from
the ring map whose `Spec` is `Y.isoSpec.inv ≫ g` (`Spec.preimage`). `algebraMap_coordinateRing_eq` proves that the two algebra maps from `K`
agree. Both `Spec` images equal `Y.isoSpec.inv ≫ g`, by `coordinateIso_hom_over`
and `affineCoordinateSpecMap`, and `Spec.map` is injective.
`coordinateAlgEquiv g : CoordinateRing g ≃ₐ[K] AffineCoordinateRing K (Over.mk
g)` is therefore the identity of `Γ(Y, ⊤)`, as a `K`-algebra equivalence.
`coordinateAlgEquiv_apply` records that it is the identity on elements.

## Points of affine opens

For an affine open `U : X.affineOpens`, the published relative scheme
`openOver K (Over.mk f) U` is the open subscheme `U` over `Spec K`.
Its relative `K`-points are the published type `RingPoint K (openOver K
(Over.mk f) U) K`.

`affineAlgPoint K f U q` is the `K`-algebra map from `CoordinateRing
(structureMap f U)` to `K` defined by such a point `q`. It precomposes the
published equivalence `affineSchemePointEquiv`, from relative points to
`K`-algebra maps out of `AffineCoordinateRing`, with `coordinateAlgEquiv`.
`localAnalyticPoint K f U q : LocalSpace K f U` is the published analytic point
`AffineAnalytification.analyticPoint` of `affineAlgPoint K f U q`, for the
chosen presentation `chartPresentation K f U`. This is the character of a
polynomial-locus chart given by evaluation at the coordinates of `q`.

## Points of the glued space

For an actual relative `K`-point `p : RingPoint K (Over.mk f) K` of `X`, the
published theorem `exists_affineOpenPoint` gives an affine open through which
`p` factors. `pointAffine K f p` is a chosen such open, and `pointLift K f p` is
a chosen factorization of `p` through it. `openPointMap_pointLift` proves that
composing `pointLift K f p` with the open immersion gives `p` back.

`analyticRationalPoint K f p : Space K f` is `ι K f (pointAffine K f p)` applied
to `localAnalyticPoint K f (pointAffine K f p) (pointLift K f p)`.
`analyticRationalPoint_def` unfolds this definition, and
`analyticRationalPoint_mem_range` records that the point lies in the image of
the chosen affine open.

## Scope

The module does not prove that `analyticRationalPoint` is independent of the
chosen affine open and factorization. It does not prove that it is injective,
that its image consists of the points with residue field `K`, or that it is a
topological embedding for the published point topology of `X(K)`. It also does
not prove that `ι K f U` is injective or open. Those facts need the gluing
statements; `SchemeAnalytificationOpenGluing` proves that `ι K f U` is an open
embedding (`OpenGluing.isOpenEmbedding_ι`). Nothing here concerns field
extensions of `K` or algebraic spaces.
