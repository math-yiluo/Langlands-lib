# Statement: the glued analytification space of a scheme is an open gluing

This module states, without proof, the basic topological properties of the glued
analytification space `Space K f` of a scheme `X` locally of finite type over a
complete nonarchimedean field `K`. `Space K f` is constructed in
`SchemeAnalytificationSpace`. The proposition is
`Langlands.Analytic.SchemeAnalytification.SchemeAnalytificationGluingStatement`.

## Provenance

Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*
(1990), §3.4 ("GAGA: the case of nontrivial valuation"), proof of Theorem 3.4.1,
printed pp.63–64/PDF pp.77–78. Step (2) states that for an open subscheme
`X ⊆ Y` with canonical morphism `π : Y^an → Y`, the open subset `π^{-1}(X)`
of `Y^an` is `X^an`. Step (3) covers an arbitrary `X` by open affine subschemes
and glues their analytifications, using the universal property and step (2).
Theorem 3.4.8(i), printed p.67/PDF p.81, states that `X` is separated if and
only if `|X^an|` is Hausdorff. Throughout §3.4 `X` is a scheme locally of finite
type over a non-Archimedean field `k` with nontrivial valuation. The registered
source is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.

Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed
p.19, final paragraph of the proof of Proposition 5.11(3), uses the
analytification of [CT] and its compatibility with open immersions and with the
scheme case. Conrad–Temkin, *Non-archimedean analytification of algebraic
spaces* (2009), Theorem 2.2.3, printed pp.7–8, builds the analytification of
algebraic spaces from that of schemes. The registered sources are
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`, and
`conrad-temkin-2009-nonarchimedean-analytification`, SHA256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`.

The formulation below is derived. Berkovich proves the gluing for analytic
spaces with their structure sheaves and a chosen affine covering. Here it is
stated for the underlying topological spaces of the Library's polynomial-locus
model, glued over all affine opens and all inclusions between them. Items (1)
to (4) are the topological content of steps (2) and (3) in this model. Item (5)
is Theorem 3.4.8(i) for the glued space. No numbered source statement asserts
item (3) on intersections, which expresses that the gluing data agree on
overlaps.

## Hypotheses

`K : Type u` is a nontrivially normed field that is ultrametric
(`IsUltrametricDist K`) and complete. `X : Scheme.{u}` is a scheme in the
universe of `K`, and `f : X ⟶ Spec (CommRingCat.of K)` is its structure
morphism, assumed `LocallyOfFiniteType`. No quasi-compactness, separatedness,
reducedness or nonemptiness of `X` is assumed, except that item (4) assumes
`IsAffine X` and item (5) characterizes separatedness.

## Statement

The proposition is the conjunction of five items, for all such `K`, `X` and `f`.

1. For affine opens `V ≤ U` of `X`, the continuous map `localMap K f h` from
   the analytification of `V` to that of `U` is an open embedding
   (`IsOpenEmbedding`). It is induced by restricting global sections from `U`
   to `V`.
2. For every affine open `U`, the canonical map `ι K f U` from the
   analytification of `U` into `Space K f` is an open embedding.
3. For affine opens `U` and `V`, the intersection of the ranges of `ι K f U`
   and `ι K f V` equals the union of the ranges of `ι K f W` over all affine
   opens `W ≤ U ⊓ V`.
4. If `X` is affine, then the canonical map `ι K f ⟨⊤, isAffineOpen_top X⟩`
   from the analytification of the affine open `⊤` is a homeomorphism
   (`IsHomeomorph`) onto `Space K f`.
5. `IsSeparated f` holds if and only if `Space K f` is Hausdorff (`T2Space`).

The local analytifications `LocalSpace K f U` are the published spaces
`AffineAnalytification.Space K (chartPresentation K f U)` for the chosen
finite polynomial presentation of the global sections of `U`. In Berkovich's
terms they are the spaces of multiplicative seminorms on these global sections
extending the norm of `K` (Remark 3.4.2, printed p.64/PDF p.78).

## Scope

The module supplies no proof; `SchemeAnalytificationGluingProof` proves the
statement as `schemeAnalytificationGluing`. It states nothing about an analytic
structure sheaf or affinoid atlas on `Space K f`, about maps induced by
morphisms of schemes, about independence of the chosen presentations, about
rational points, or about the analytification of algebraic spaces.
