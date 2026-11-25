# Analytic morphisms of affine analytifications in the localized category

This module turns the published strong map of polynomial-locus analytifications
induced by a `K`-algebra map into a morphism of analytic spaces. The target is
the Library's localized category of saturated atlas presentations, which models
Berkovich's category of `K`-analytic spaces. For a `K`-algebra map `f : A → B`
with finite polynomial presentations `P` of `A` and `Q` of `B`, it constructs a
morphism `Spec(B)ᵃⁿ → Spec(A)ᵃⁿ` between the published objects
`AffineAnalytification.localized K Q` and `AffineAnalytification.localized K P`.
Its underlying continuous map is the published `AffineAnalytification.baseMap`.
The only new proof needed is a general coherence lemma for strong maps into
atlases with directed charts.

## Provenance

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
Definition 1.2.7, printed p.18/PDF p.15, defines a strong morphism of analytic
spaces with given atlases: a continuous map together with compatible morphisms
of affinoid spaces for all admissible chart pairs. Proposition 1.2.8 on the same
page extends a strong morphism uniquely to the maximal atlases of all affinoid
domains of the charts. Definition 1.2.9, printed p.19/PDF p.16, defines
quasi-isomorphisms, and printed p.20/PDF p.17 defines the category of
`K`-analytic spaces as the category of fractions with respect to them. The
registered source is `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`. The
Library's `saturationExtension`, `SaturatedAtlasPresentation`,
`localizationFunctor` and `LocalizedCategory` implement these notions.

Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*
(1990), Theorem 3.4.1, printed p.63/PDF p.77, defines the analytification
`X^an` of a scheme `X` locally of finite type over `k` as the `k`-analytic space
representing `𝒵 ↦ Hom_k(𝒵, X)`. Hence a morphism of such schemes induces a
morphism of their analytifications, by the Yoneda lemma. On affine
schemes, steps (1)–(3) of its proof, printed p.64/PDF p.78, realize the
analytification as the polynomial locus exhausted by closed polydiscs. The
registered source is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.
Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed
p.19, final paragraph of the proof of Proposition 5.11(3), uses this functorial
analytification. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The coherence lemma is a derived step and is not a numbered statement of the
sources. It verifies, for the Library's atlases, the hypothesis that the
Library's implementation of Proposition 1.2.8 requires.

## Hypotheses

In the general section, `K` is a complete ultrametric normed field, and `A` and
`B` are `AffinoidAtlasPresentation`s in universes `u, v, w`. In the affine
section, `K` is a nontrivially normed, ultrametric and complete field in
universe `u`. The algebras `A : Type v` and `B : Type w` are arbitrary
commutative `K`-algebras with finite polynomial presentations
`P : FinitePolynomialPresentation K A` and `Q : FinitePolynomialPresentation K B`.
The map `f : A →ₐ[K] B` is an arbitrary `K`-algebra map. No reducedness,
positive arity or nonemptiness is assumed.

## Coherence for directed targets

`AffinoidAtlasPresentation.StrongHom.hasCoherentPullbacks_of_hasDirectedCharts`
proves that every strong map `f : StrongHom A B` satisfies the Library's
`HasCoherentPullbacks` when the target atlas has directed charts
(`B.atlas.HasDirectedCharts`). Coherence asks that the bounded pullbacks of a
source chart `i` to two admissible target charts `j` and `k` agree on every
common subchart `m`, tested against every presented affinoid algebra. The
proof chooses a target chart `q` containing both `j` and `k`. The restriction
law `restriction_comm` of `f`, with the identity restriction of chart `i`,
shows that the pullbacks to `j` and to `k` both become the pullback to `q`
after composing with the atlas restrictions into `q`. The transitivity law
`restriction_comp` of the target atlas, and cancellation of a restriction map
(`restriction_hom_ext`, from domain factorization uniqueness), then give the
required equation.

## The saturated and localized morphisms

All remaining declarations lie in `Langlands.Analytic.AffineAnalytification`.
`strongHom_hasCoherentPullbacks K P Q f` applies the coherence lemma to the
published `strongHom K P Q f : StrongHom (presentation K Q) (presentation K P)`.
The target atlas has directed charts by the published `atlas_hasDirectedCharts`.

`saturatedHom K P Q f : saturated K Q ⟶ saturated K P` is a morphism in the
category of saturated presentations. It is the Library's `saturationExtension`
of `strongHom K P Q f`, the extension of the bounded pullbacks to all full local
affinoid domains of both atlases, following Proposition 1.2.8.

`localizedHom K P Q f : localized K Q ⟶ localized K P` is the image of
`saturatedHom K P Q f` under `localizationFunctor`. It is the morphism of
analytic spaces `Spec(B)ᵃⁿ → Spec(A)ᵃⁿ` induced by `f`.

`saturatedHom_baseMap` records that the underlying continuous map of
`saturatedHom K P Q f` is `baseMap K P Q f`, definitionally.
`localizedSpaceFunctor_map_localizedHom` proves that `localizedSpaceFunctor`
sends `localizedHom K P Q f` to `TopCat.ofHom (baseMap K P Q f)`, by the
published `localizedSpaceFunctor_map`.

## Scope

The module proves no functoriality of `localizedHom`, such as identities or
composites. Those depend on the published affine functoriality statement
`AffineAnalytificationFunctorialityStatement`, which the Library proves as
`affineAnalytificationFunctoriality` in `AffineAnalytificationFunctorialityProof`;
the functoriality of `localizedHom` itself is
`AffineAnalytificationLocalizedFunctorialityStatement`, proved in
`AffineAnalytificationLocalizedFunctorialityProof`. It does not compare morphisms for two
presentations of the same algebra. It proves nothing about immersions, rational
points, the center map or the scheme-level glued space. Those lie outside this
module.
