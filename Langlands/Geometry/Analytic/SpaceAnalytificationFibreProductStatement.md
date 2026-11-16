# Analytifications of algebraic spaces preserve fibre products

`SpaceAnalytificationFibreProductStatement` says the following. Let `K` be a
complete ultrametric nontrivially normed field. Let `W` be a fibre product of
morphisms `f₁ : X₁ ⟶ Z` and `f₂ : X₂ ⟶ Z` of algebraic spaces over `Spec K`,
with projections `π₁ : W ⟶ X₁` and `π₂ : W ⟶ X₂`, where `X₁`, `X₂` and `Z` are
separated and locally of finite type. Given analytifications of `W`, `X₁`, `X₂`
and `Z`, and morphisms between them compatible with the four morphisms of
algebraic spaces, the resulting square of analytic spaces is a pullback square.
This module states the proposition only; it supplies no proof.

## Statement

The statement quantifies over a universe `u` and:
- a field `K : Type u` with `NontriviallyNormedField K`, `IsUltrametricDist K`
  and `CompleteSpace K`;
- algebraic spaces `W`, `X₁`, `X₂` and `Z` over `Spec (CommRingCat.of K)` and
  morphisms `π₁ : W ⟶ X₁`, `π₂ : W ⟶ X₂`, `f₁ : X₁ ⟶ Z`, `f₂ : X₂ ⟶ Z`;
- the hypothesis `IsPullback π₁ π₂ f₁ f₂` in the category of algebraic spaces
  over `Spec K` (Mathlib's `IsPullback`: the square commutes and is a limit
  cone);
- hypotheses `IsSeparated` and `LocallyOfFiniteTypeOverBase` for `X₁`, `X₂`
  and `Z`;
- objects `V`, `Y₁`, `Y₂` and `T` of `LocalizedCategory.{u, u, u}`, families
  `q : PointFamily K W V`, `p₁ : PointFamily K X₁ Y₁`,
  `p₂ : PointFamily K X₂ Y₂` and `r : PointFamily K Z T`, and the four
  hypotheses `IsAnalytification K W V q`, `IsAnalytification K X₁ Y₁ p₁`,
  `IsAnalytification K X₂ Y₂ p₂` and `IsAnalytification K Z T r`;
- morphisms `Φ₁ : V ⟶ Y₁`, `Φ₂ : V ⟶ Y₂`, `F₁ : Y₁ ⟶ T` and `F₂ : Y₂ ⟶ T`
  with the compatibilities, for all commutative `K`-algebras `A` in universe
  `u`, finite polynomial presentations `P` of `A` and points `x`:
  `q A P x ≫ Φ₁ = p₁ A P (RingPoints.map π₁ x)`,
  `q A P x ≫ Φ₂ = p₂ A P (RingPoints.map π₂ x)`,
  `p₁ A P x ≫ F₁ = r A P (RingPoints.map f₁ x)` and
  `p₂ A P x ≫ F₂ = r A P (RingPoints.map f₂ x)`.

The conclusion is `IsPullback Φ₁ Φ₂ F₁ F₂` in `LocalizedCategory`. This
includes commutativity `Φ₁ ≫ F₁ = Φ₂ ≫ F₂` and the universal property of the
pullback in the Library's localized category.

No separatedness or finiteness hypothesis is placed on `W`. The fibre product
of separated algebraic spaces locally of finite type over `K` has both
properties, but the statement only uses the given analytification `(V, q)`.
By `SpaceAnalytificationMorphismStatement`, each of `Φ₁`, `Φ₂`, `F₁` and `F₂`
is the unique morphism compatible with the corresponding morphism of
algebraic spaces. This statement does not depend on that one; it takes the
four morphisms as hypotheses.

## Provenance

The source is Conrad–Temkin, *Non-archimedean analytification of algebraic
spaces* (2009), registered as
`conrad-temkin-2009-nonarchimedean-analytification`, SHA256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`.
- Theorem 2.2.3, printed pp.7–8 (rigid-analytic setting): `X ↦ Xᵃⁿ` is a
  functor on analytifiable algebraic spaces, and it is compatible with fibre
  products.
- Printed p.19, last paragraph of §4.1: when the `k`-analytic quotient exists,
  it "is functorial in `X` in a manner that respects the formation of fiber
  products and Zariski-open and Zariski-closed immersions".
- Printed p.11, proof of Corollary 2.2.6, uses "the compatibility of
  analytification and fiber products" to identify `Δ_{fᵃⁿ}` with `(Δ_f)ᵃⁿ`.

The affine scheme case is Berkovich, *Étale cohomology for non-Archimedean
analytic spaces* (1993), registered as `berkovich-1993-etale-cohomology`,
SHA256 `06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.
Proposition 2.6.1, printed p.51/PDF p.48, states that `𝒴 ↦ 𝒴ᵃⁿ` commutes with
fibred products. Its affine case over `K` is the Library's
`AffineAnalytificationFibreProductStatement`.

The second source is Conrad, *Weil and Grothendieck approaches to adelic points*
(2011), registered as `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. Printed
p.19, proof of Proposition 5.11(3), describes the analytification of [CT] for
separated algebraic spaces locally of finite type as "compatible with fiber
products", among other properties.

The formulation is derived. Conrad works with rigid-analytic spaces; this
statement uses the `k`-analytic analytification of Conrad–Temkin §4, modelled
by `IsAnalytification`, with analytic spaces in the Library's localized
category. The fibre product `W` is given by a pullback square, not by a chosen
construction, and the analytified morphisms are given by their compatibility
hypotheses. Only nontrivially normed `K` is treated, as the Library's affine
analytifications require.

## Why the statement should be true

This is not a Lean proof. Commutativity: `Φ₁ ≫ F₁` and `Φ₂ ≫ F₂` are both
compatible with `π₁ ≫ f₁ = π₂ ≫ f₂`, and morphisms out of `V` are determined by
their composites with the maps `q(x)`. The maps `q(x)` for étale points `x` are
étale and jointly surjective, and representable functors are étale sheaves.

For the universal property, choose étale points of `Z`, `X₁` and `X₂` by affine
schemes such that the points `Spec A₁ → X₁` and `Spec A₂ → X₂` lie over a point
`Spec C → Z`. Then `Spec A₁ ×_{Spec C} Spec A₂ = Spec(A₁ ⊗_C A₂)` maps étale to
`W`. These étale points cover `W`. By the affine case, `Spec(A₁ ⊗_C A₂)ᵃⁿ` is
the fibre product `Spec(A₁)ᵃⁿ ×_{Spec(C)ᵃⁿ} Spec(A₂)ᵃⁿ`. The analytic fibre
product `Y₁ ×_T Y₂` is covered étale by the products
`Spec(A₁)ᵃⁿ ×_T Spec(A₂)ᵃⁿ`. The pullback condition of `IsAnalytification`,
applied to the étale point `Spec C → Z`, identifies these with the fibre
products over `Spec(C)ᵃⁿ` after restricting along the covering. Gluing along
the overlaps, which are again analytifications of affine fibre products by the
pullback condition for `W`, identifies `V` with `Y₁ ×_T Y₂`. This follows
Conrad–Temkin's proof of Theorem 2.2.3 with the étale quotient criterion of
their Definition 4.1.1. The proof must also realize these facts in the
Library's localized category.
