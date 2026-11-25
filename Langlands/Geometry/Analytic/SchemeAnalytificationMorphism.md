# Analytifications of morphisms of schemes: local maps and the compatibility predicate

This module prepares the analytification of a morphism `g : X ⟶ Y` of schemes
locally of finite type over a complete nonarchimedean field `K`, in the
Library's glued model `SchemeAnalytification.Space`. For affine opens `U` of
`X` and `V` of `Y` with `g(U) ⊆ V` it constructs the continuous map
`Uᵃⁿ → Vᵃⁿ` of affine analytifications induced by `g`. It then defines the
predicate saying that a continuous map `Space K f → Space K f'` restricts to
these local maps. The module constructs no map of glued spaces for a general
`g`. It proves no existence or uniqueness of a map satisfying the predicate,
except for the identity morphism. The image of an affine open of `X` need not
lie in an affine open of `Y`, so existence needs the open-covering properties
of the glued space. Those are stated in
`SchemeAnalytificationGluingStatement`, which `SchemeAnalytificationGluingProof`
proves as `schemeAnalytificationGluing`.

## Provenance

Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*
(1990), Theorem 3.4.1, printed p.63/PDF p.77, defines the analytification
`X^an` of a scheme `X` locally of finite type over `k` as the representing
object of the functor `𝒵 ↦ Hom_k(𝒵, X)` on `k`-analytic spaces. Step (2) of
its proof, printed p.64/PDF p.78, identifies the analytification of an open
subscheme with the inverse image of that open subscheme in `Y^an`. Step (3)
glues the analytifications of affine opens. By the Yoneda lemma, a standard
consequence that Berkovich does not spell out, a morphism `g : X → Y` induces a
morphism `g^an : X^an → Y^an`. Then `g^an` maps the analytification of an
affine open `U` into that of any open `V ⊇ g(U)`, and there it is the
analytification of the restriction `U → V`. The registered source is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.

Conrad–Temkin, *Non-archimedean analytification of algebraic spaces* (2009),
Theorem 2.2.3 and its proof, printed pp.7–8, define `f^an` for algebraic spaces
through étale charts and show that it does not depend on the charts. The
registered source is `conrad-temkin-2009-nonarchimedean-analytification`,
SHA256 `ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`.
Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed
p.19, final paragraph of the proof of Proposition 5.11(3), relies on this
functorial analytification. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The sources characterize `g^an` by a universal property. No source writes the
local description below as a definition. The formulation is derived for the
Library's explicit model. There, the analytification of an affine open is the
published polynomial-locus space of its global sections. The maps between
those spaces are the published `AffineAnalytification.baseMap` of
`K`-algebra maps.

## Hypotheses

All declarations lie in `Langlands.Analytic.SchemeAnalytification`. In the
algebraic section `K` is any commutative ring, and `X`, `Y` and `Z` are schemes
in universe `u`, the universe of `K`. The structure morphisms
`f : X ⟶ Spec (CommRingCat.of K)`, `f' : Y ⟶ Spec (CommRingCat.of K)` and
`f'' : Z ⟶ Spec (CommRingCat.of K)` are arbitrary. A morphism `g : X ⟶ Y` over
`Spec K` comes with `hg : g ≫ f' = f`. In the normed section `K` is a
nontrivially normed, ultrametric and complete field, and `f` and `f'` are
`LocallyOfFiniteType`. No quasi-compactness, separatedness, reducedness or
nonemptiness is assumed.

## Coordinate maps between affine opens

Let `U : X.affineOpens`, `V : Y.affineOpens` and `h : U ≤ g ⁻¹ᵁ V`.
`openCoordinateMap g hg h` is the `K`-algebra map
`CoordinateRing (structureMap f' V) →ₐ[K] CoordinateRing (structureMap f U)`.
It is the published `coordinateMap` of Mathlib's restriction
`g.resLE V U h : U ⟶ V` of `g`. That restriction is over `Spec K` by
`Scheme.Hom.resLE_comp_ι` and `hg`. `openCoordinateMap_apply` records that the
underlying function is `(g.resLE V U h).appTop` on global sections.

`openCoordinateMap_id` states that for the identity of `X` and `h : U ≤ V` the
map is the published restriction `restriction f h`, by Mathlib's
`Scheme.Hom.resLE_id`. `openCoordinateMap_comp` states that for `g : X ⟶ Y`,
`g' : Y ⟶ Z`, affine opens `U`, `V`, `W` and inclusions `h : U ≤ g ⁻¹ᵁ V`,
`h' : V ≤ g' ⁻¹ᵁ W` and `h'' : U ≤ (g ≫ g') ⁻¹ᵁ W`, the map of `g ≫ g'` is the
composite `(openCoordinateMap g hg h).comp (openCoordinateMap g' hg' h')`. The
proof uses Mathlib's `Scheme.Hom.resLE_comp_resLE` and `Scheme.Hom.comp_appTop`.

## Local maps of analytifications

`morphismLocalMap K f f' g hg h : C(LocalSpace K f U, LocalSpace K f' V)` is
`AffineAnalytification.baseMap K (chartPresentation K f' V)
(chartPresentation K f U) (openCoordinateMap g hg h)`. It is the continuous
map of polynomial-locus analytifications induced by `Γ(V) → Γ(U)`.
`morphismLocalMap_id` states that for the identity of `X` and `h : U ≤ V` it
is the published gluing map `localMap K f h`.

## The compatibility predicate

`IsAnalytificationMap K f f' g hg F` is a `Prop` about a continuous map
`F : C(Space K f, Space K f')`. It holds when
`F (ι K f U y) = ι K f' V (morphismLocalMap K f f' g hg h y)` for every affine
open `U` of `X`, every affine open `V` of `Y`, every `h : U ≤ g ⁻¹ᵁ V` and
every point `y` of `LocalSpace K f U`. Here `ι` is the published canonical map
from the analytification of an affine open into the glued space. The
predicate imposes the condition only on pairs with `g(U) ⊆ V`, and it imposes
it for all such pairs. In the sources, the analytification `g^an` restricts
on `U^an` to the analytification of `U → V` for every such pair.

`isAnalytificationMap_id` proves that the identity of `Space K f` satisfies
the predicate for the identity morphism. The proof combines
`morphismLocalMap_id` with the published gluing identity `ι_localMap`.
`IsAnalytificationMap.apply_eq` proves that two maps satisfying the predicate
for the same `g` agree at `ι K f U y` whenever `U` maps into some affine open
`V` of `Y`.

## Scope

The module does not construct a continuous map `Space K f → Space K f'` for a
general `g`. It does not prove that such a map exists or is unique;
`SchemeAnalytificationMorphismProof` constructs it and proves
`existsUnique_isAnalytificationMap`. It does not prove that local maps respect
composition: that needs the published affine functoriality statement
`AffineAnalytificationFunctorialityStatement`, which
`AffineAnalytificationFunctorialityProof` proves as
`affineAnalytificationFunctoriality`. It proves no compatibility with the
center map to `X`, with rational points, with fibre products or with
immersions.
