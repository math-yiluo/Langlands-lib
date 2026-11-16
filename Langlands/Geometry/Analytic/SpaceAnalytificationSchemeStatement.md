# Analytifications of separated schemes as algebraic spaces

`SpaceAnalytificationSchemeStatement` says the following. Let `K` be a
complete ultrametric nontrivially normed field and `X` a separated scheme
locally of finite type over `K`, with structure morphism `f`. Let `(Y, p)` be an
analytification, in the sense of `IsAnalytification`, of the algebraic space
`(schemeToSpace _).obj (Over.mk f)` attached to `X`. Then the underlying space
of `Y` is homeomorphic to the Library's glued analytification space
`SchemeAnalytification.Space K f` of `X`. The homeomorphism is compatible with
the affine open charts and with `K`-rational points. This module states the
proposition only; it supplies no proof.

## Statement

The statement quantifies over a universe `u` and:
- a field `K : Type u` with `NontriviallyNormedField K`, `IsUltrametricDist K`
  and `CompleteSpace K`;
- a scheme `X : Scheme.{u}` and a morphism `f : X ⟶ Spec (CommRingCat.of K)`
  with `LocallyOfFiniteType f` and Mathlib's `IsSeparated f`;
- `Y : LocalizedCategory.{u, u, u}`, a family
  `p : PointFamily K ((schemeToSpace _).obj (Over.mk f)) Y` and the hypothesis
  `IsAnalytification K ((schemeToSpace _).obj (Over.mk f)) Y p`.

The conclusion is the existence of a homeomorphism
`e : localizedSpaceFunctor.obj Y ≃ₜ Space K f` with two properties.
1. Charts. Let `U` be an affine open of `X`, and let `x` be a test point of the
   algebraic space with values in `CoordinateRing (structureMap f U)`, the
   global sections of `U`. Suppose that the scheme morphism
   `(schemeRingPointsEquiv K (Over.mk f) _ x).left` equals
   `(coordinateIso (structureMap f U)).inv ≫ U.ι`, the composite of the
   canonical isomorphism from the spectrum of the global sections to `U` with
   the inclusion of `U` into `X`. Then for every point `y` of `LocalSpace K f U`,
   `e` sends the image of `y` under
   `localizedSpaceFunctor.map (p _ (chartPresentation K f U) x)` to
   `ι K f U y`. Here `chartPresentation K f U` is the Library's chosen
   presentation of the global sections of `U`. `LocalSpace K f U` is its affine
   analytification and `ι K f U` is the canonical map into `Space K f`.
2. Rational points. For every finite polynomial presentation `P₀` of `K` and
   every `K`-point `x` of the algebraic space, `e (rationalPoint p P₀ x)`
   equals `analyticRationalPoint K f (schemeRingPointsEquiv K _ K x)`. This is
   the point of `Space K f` attached to the corresponding `K`-point of `X`.

`schemeRingPointsEquiv` identifies the test points of the algebraic space of
`X` with relative scheme points. For every affine open `U` there is exactly one
test point `x` satisfying the hypothesis of property 1. The composite
`(coordinateIso _).inv ≫ U.ι` lies over `Spec K` by `coordinateIso_hom_over`.

The statement compares underlying topological spaces only. It does not claim
that `e` comes from an isomorphism in `LocalizedCategory` between `Y` and an
analytic structure on `Space K f`. That structure is the subject of the
published `SchemeAnalytificationAnalyticStructureStatement`. The scheme case
is stated for separated `X`, the scope of `IsAnalytification`.

## Provenance

The first source is Conrad, *Weil and Grothendieck approaches to adelic points*
(2011), registered as `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. Printed
p.19, proof of Proposition 5.11(3), describes the analytification of [CT] for
separated algebraic spaces locally of finite type over `k`. Among other
properties it is compatible with "the scheme case".

The second source is Conrad–Temkin, *Non-archimedean analytification of
algebraic spaces* (2009), registered as
`conrad-temkin-2009-nonarchimedean-analytification`, SHA256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`.
- Definition 2.2.2 and Lemma 2.2.1, printed p.7: `Xᵃⁿ` is the étale quotient
  `Uᵃⁿ/Rᵃⁿ` for any étale chart `R ⇒ U` of `X`, independent of the chart up to
  unique isomorphism.
- Definition 4.1.1, printed p.18: the `k`-analytic quotient of an étale
  equivalence relation. On the same page, schemes are analytified by
  Berkovich's functor [Ber2, 2.6.1].
- Printed p.19, last paragraph of §4.1: the `k`-analytic quotient is
  independent of the chart and its formation is Zariski-local on `X`.

For a scheme `X` the chart `X ⇒ X`, with both maps the identity, has quotient
the scheme analytification `Xᵃⁿ`. So the scheme case follows from the
independence of the chart. This deduction is not printed in either source.

The third source is Berkovich, *Spectral Theory and Analytic Geometry over
Non-Archimedean Fields* (1990), registered as
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.
Theorem 3.4.1, printed pp.63–64/PDF pp.77–78, constructs `Xᵃⁿ` for a scheme
locally of finite type. Step (2) of its proof identifies the analytification of
an open subscheme with an open subset of `Yᵃⁿ`. Step (3) glues the
analytifications of an affine open cover. The Library's `Space K f`, from
`SchemeAnalytificationSpace`, is this gluing over all affine opens. Its
topological properties are stated in the published
`SchemeAnalytificationGluingStatement`.

The formulation is derived. Conrad and Conrad–Temkin compare analytic spaces;
this statement compares the underlying space of an analytification in the
sense of `IsAnalytification` with the Library's glued space, through a
homeomorphism and its compatibility with charts and rational points. Only
nontrivially normed `K` is treated, as the Library's affine analytifications
require.

## Why the statement should be true

This is not a Lean proof. For an affine open `U`, write `x_U` for the test point
in property 1. Its scheme morphism `Spec Γ(U) ≅ U ⟶ X` is an open immersion,
hence étale, so `p(x_U)` is étale.

Define `g : Space K f → localizedSpaceFunctor.obj Y` on the image of `U` by the
underlying map of `p(x_U)`. For affine opens `V ≤ U`, naturality of `p` along
the restriction `Γ(U) → Γ(V)` gives `p(x_V) = localizedHom (restriction) ≫ p(x_U)`.
So these maps agree on the gluing relation and descend, via `desc`, to a
continuous map `g`.

`g` is injective. Let `U`, `U'` be affine opens. Since `X` is separated,
`U ∩ U'` is affine, and the square formed by `Spec Γ(U ∩ U')`, `Spec Γ(U)`,
`Spec Γ(U')` and `X` is a pullback of presheaves. The pullback condition of
`IsAnalytification` makes the analytification of `U ∩ U'` the fibre product of
those of `U` and `U'` over `Y`. Every pair of points with a common image in `Y`
lifts to a point of a fibre product of analytic spaces. So two points of the
charts with a common image in `Y` come from one point of the analytification
of `U ∩ U'`, and they are identified in `Space K f`.

`g` is surjective. Every point of `Y` lies in the image of `p(x)` for some
étale test point `x : Spec A → X`. Cover `Spec A` by affine opens `W`, each
mapping into an affine open `U` of `X`. Their analytifications cover that of
`Spec A`. By naturality, the map attached to the restriction of `x` to `W`
factors through both `p(x)` and `p(x_U)`.

`g` is open. Each composite of `g` with a chart map is the underlying map of the
étale morphism `p(x_U)`, and étale morphisms of analytic spaces are open. An
open set of `Space K f` is the union of the images of its preimages in the
charts. So its image under `g` is open. Thus `g` is a homeomorphism; let `e` be
its inverse. Property 1 holds by construction.

For property 2, let `x` be a `K`-point. It factors through an affine open `U`
via an algebra map `φ : Γ(U) → K`. Naturality gives
`p(x) = localizedHom φ ≫ p(x_U)`. So `rationalPoint p P₀ x` is the image under
`p(x_U)` of the analytic point of `φ`. By property 1, `e` sends it to the point
of `Space K f` given by `U` and `φ`, which is `analyticRationalPoint K f x` by
the gluing relation.
