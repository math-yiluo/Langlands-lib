# Statement: analytifications of morphisms of schemes exist, are unique and are functorial

This module states, without proof, that every morphism of schemes locally of
finite type over `K` has exactly one analytification in the Library's glued
polynomial-locus model. It also states that this map is compatible with
Berkovich's center maps and with `K`-rational points, and that analytifications
compose. The predicate `IsAnalytificationMap` and the local maps it uses are
defined in `SchemeAnalytificationMorphism`. The proposition is
`Langlands.Analytic.SchemeAnalytification.SchemeAnalytificationMorphismStatement`.

## Provenance

Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*
(1990), §3.4, Theorem 3.4.1, printed p.63/PDF p.77, defines the analytification
`X^an` of a scheme `X` locally of finite type over `k` as the representing
object of the functor `𝒵 ↦ Hom_k(𝒵, X)` on `k`-analytic spaces, together with
`π : X^an → X`. Step (2) of the proof, printed p.64/PDF p.78, identifies the
analytification of an open subscheme with its inverse image under `π`. Step (3)
glues the analytifications of affine opens. Section 3.4 assumes a nontrivial
valuation, as `NontriviallyNormedField` does here. The registered source is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.

By the Yoneda lemma, a standard consequence that Berkovich does not spell out,
a morphism `g : X → Y` induces a unique `g^an : X^an → Y^an` with
`π_Y ∘ g^an = g ∘ π_X`, and `(g' ∘ g)^an = g'^an ∘ g^an`. A `k`-point of `X` is
a morphism `Spec k → X`. Its analytic point is the image of the analytification
of `Spec k`, a single point. So `g^an` sends the analytic point of `p` to that
of `g ∘ p`.

Conrad–Temkin, *Non-archimedean analytification of algebraic spaces* (2009),
Theorem 2.2.3 and its proof, printed pp.7–8, define `f^an` for algebraic spaces.
They show that it does not depend on the charts and is compatible with
composition, so analytification is a functor. The registered source is
`conrad-temkin-2009-nonarchimedean-analytification`, SHA256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`.
Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed
p.19, final paragraph of the proof of Proposition 5.11(3), relies on this
functorial analytification. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The formulation is derived for the Library's model, in which the sources'
universal property is replaced by the explicit predicate `IsAnalytificationMap`.
In this model the items depend on facts that are stated separately in the
Library. The image of an affine open of `X` need not lie in an affine open
of `Y`. So existence and uniqueness need the published
`SchemeAnalytificationGluingStatement`, in which the canonical maps are open
embeddings, and item (5) of the published `AnalytificationCenterStatement`, which
identifies the analytification of an affine open with the inverse image of that
open under the center map. Items (2)–(4) also use the published affine
functoriality statement `AffineAnalytificationFunctorialityStatement`. Item (3)
also uses the published `SchemeAnalytificationRationalPointsStatement` and the
naturality of affine rational points `AffineAnalytificationRationalPointNaturalityStatement`.
The Library proves these statements as `schemeAnalytificationGluing`,
`analytificationCenter`, `affineAnalytificationFunctoriality`,
`schemeAnalytificationRationalPoints` and
`affineAnalytificationRationalPointNaturality`, in the modules named after
each statement with `Proof` in place of `Statement`.

## Hypotheses

`K : Type u` is a nontrivially normed field that is ultrametric
(`IsUltrametricDist K`) and complete. `X`, `Y` and `Z` are schemes in the
universe of `K`, with structure morphisms
`f : X ⟶ Spec (CommRingCat.of K)`, `f' : Y ⟶ Spec (CommRingCat.of K)` and
`f'' : Z ⟶ Spec (CommRingCat.of K)`, each assumed `LocallyOfFiniteType`.
`g : X ⟶ Y` and `g' : Y ⟶ Z` are morphisms over `Spec K`, recorded by
`hg : g ≫ f' = f` and `hg' : g' ≫ f'' = f'`. No separatedness,
quasi-compactness, reducedness or nonemptiness is assumed.

## Statement

The proposition is the conjunction of two parts.

First part, for all such `K`, `X`, `Y`, `f`, `f'`, `g` and `hg`:

1. There is exactly one continuous map
   `F : C(Space K f, Space K f')` with `IsAnalytificationMap K f f' g hg F`.
   That predicate says that
   `F (ι K f U y) = ι K f' V (morphismLocalMap K f f' g hg h y)` for all affine
   opens `U` of `X` and `V` of `Y`, every `h : U ≤ g ⁻¹ᵁ V` and every point `y`
   of the analytification of `U`.

   Every continuous map `F` satisfying the predicate also has two further
   properties:

2. For every `z : Space K f`, `center K f' (F z) = g (center K f z)`. Here
   `center` is the published center map from `AnalytificationCenter`, and
   `g (·)` is the underlying map of points of `g`.
3. For every `K`-point `p : RingPoint K (Over.mk f) K` of `X`,
   `F (analyticRationalPoint K f p)` equals
   `analyticRationalPoint K f' (p ≫ Over.homMk g hg)`. Here
   `analyticRationalPoint` is the published point of the glued space defined by
   a `K`-point, and `p ≫ Over.homMk g hg` is the `K`-point `g ∘ p` of `Y`.

Second part, for all such `K`, `X`, `Y`, `Z`, structure morphisms, `g`, `hg`,
`g'` and `hg'`:

4. If `F : C(Space K f, Space K f')` satisfies the predicate for `g` and
   `F' : C(Space K f', Space K f'')` satisfies it for `g'`, then the composite
   `F'.comp F` satisfies it for `g ≫ g'`. The proof that `g ≫ g'` is over
   `Spec K` is supplied inside the statement from `hg` and `hg'`.

The identity case, that `ContinuousMap.id` satisfies the predicate for the
identity morphism, is already proved as `isAnalytificationMap_id` in
`SchemeAnalytificationMorphism`. Together with items (1) and (4), it makes
`X ↦ Space K f` a functor on schemes locally of finite type over `K`.

## Scope

The module supplies no proof; `SchemeAnalytificationMorphismProof` proves the
statement as `schemeAnalytificationMorphism`. It imports
`SchemeAnalytificationMorphism`, `AnalytificationCenter` and
`SchemeAnalytificationRationalPoints`. It states nothing about open or closed
immersions, étale maps, fibre products, extension of the ground field,
structure sheaves, or independence of the chosen presentations.
