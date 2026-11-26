# Analytic quotients of étale affine chart families of separated algebraic spaces

This module contains only the Prop-valued definition
`Langlands.Analytic.SpaceAnalytification.SpaceAnalytificationChartQuotientStatement`.
It states that the étale equivalence relation of a family of étale affine charts
of a separated algebraic space has an analytic quotient (Conrad–Temkin 2009,
Theorem 4.2.2, in chart form). The file states the proposition and does not
prove it.

## Exact statement

`SpaceAnalytificationChartQuotientStatement.{u} : Prop` quantifies over:
- a field `K : Type u` with `NontriviallyNormedField K`, `IsUltrametricDist K`
  and `CompleteSpace K`;
- an algebraic space `X : AlgebraicSpace (Spec (CommRingCat.of K))` with
  `IsSeparated X`, the Library's separatedness (the diagonal of the presheaf of
  `X` is a representable closed immersion);
- an index type `ι : Type u`, commutative `K`-algebras `A i : Type u`, finite
  polynomial presentations `P i : FinitePolynomialPresentation K (A i)`, and
  ring points `x i : RingPoints K X (A i)` such that every Yoneda morphism
  `pointHom K (x i) : Spec (A i) → X` is étale (`AlgebraicSpace.IsEtale`).

The conclusion is that there are an object
`Y : LocalizedCategory.{u, u, u} (K := K)` and morphisms
`π i : AffineAnalytification.localized K (P i) ⟶ Y` such that:
1. every `π i` is étale (`SaturatedAtlasPresentation.etale`);
2. the `π i` are jointly surjective on underlying points: every
   `y : localizedSpaceFunctor.obj Y` is in the range of
   `localizedSpaceFunctor.map (π i)` for some `i`;
3. for all `i j : ι`, every commutative `K`-algebra `B : Type u` with a finite
   polynomial presentation `Q`, and all `f : A i →ₐ[K] B`, `g : A j →ₐ[K] B`:
   if the square of presheaves formed by the Yoneda images of
   `ringTestMap K f : Spec B → Spec (A i)` and `ringTestMap K g : Spec B → Spec (A j)`
   and by `pointHom K (x i)` and `pointHom K (x j)` is a pullback
   (`Spec B = Spec (A i) ×_X Spec (A j)`), then
   `IsPullback (localizedHom K (P i) Q f) (localizedHom K (P j) Q g) (π i) (π j)`
   holds in the localized category.

The family of charts need not cover `X`, and `X` is not assumed locally of
finite type: each chart is of finite type over `K` because it carries a finite
polynomial presentation. The field, the index type, the algebras and the
analytic spaces all live in the one universe `u`, so that the disjoint union of
the chart analytifications, from which the source forms the quotient, is again
an object of `LocalizedCategory.{u, u, u}`.

## Original sources

Conrad–Temkin, *Non-archimedean analytification of algebraic spaces* (2009),
registered as `conrad-temkin-2009-nonarchimedean-analytification`, SHA256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`. Printed
page numbers equal PDF page numbers in this file.
- Definition 4.1.1, p.18: a quotient of an étale equivalence relation
  `ℛ ⇉ 𝒰` of `k`-analytic spaces is a `k`-analytic space `𝒳` with an étale
  surjection `𝒰 → 𝒳` such that the two composites `ℛ ⇉ 𝒰 → 𝒳` coincide and
  `ℛ → 𝒰 ×_𝒳 𝒰` is an isomorphism.
- Theorem 4.1.2, pp.18–19, with the paragraph before it and the paragraph after
  Example 4.1.3 (p.19), together with [Ber2, 4.1.5]: representable functors on
  `k`-analytic spaces are étale sheaves, so a quotient represents the quotient
  sheaf `𝒰/ℛ` and is unique up to unique isomorphism.
- p.20, the paragraph after Theorem 4.2.1: for an étale chart `R ⇉ U` of a
  separated algebraic space, the analytified relation `ℛ ⇉ 𝒰` is an étale
  equivalence relation and `ℛ → 𝒰 × 𝒰` is a closed immersion, by Berkovich's
  dictionary [Ber2, 3.3.11].
- Theorem 4.2.2, p.20: an étale equivalence relation `ℛ ⇉ 𝒰` of `k`-analytic
  spaces with `ℛ → 𝒰 × 𝒰` a closed immersion has a quotient `𝒰/ℛ`, and it is a
  separated `k`-analytic space.
- Its proof: Lemma 4.2.3, pp.20–21 (existence of the quotient is local on `𝒰`:
  quotients over an open cover glue); Lemma 4.3.1 and Corollary 4.3.2, p.23
  (étale localization on `𝒰`); Lemma 4.3.3, pp.24–25 (local reduction to the
  quotient by a free action of a finite group); Theorem 5.1.1, p.26 (quotients
  by free actions of finite groups whose action map is a closed immersion).
- End of §4.3, p.25: Theorem 4.2.2 applied to the analytified étale chart of a
  separated algebraic space gives its analytification in the sense of
  `k`-analytic spaces (defined on p.19).

## Why the statement is expected to hold

Let `U = ⊔ᵢ Spec (A i)` and let `x : U → X` be the étale map given by the
`x i`. Since `X` is separated, `R = U ×_X U` is a closed subscheme of `U × U`.
Its components `Spec (A i) ×_X Spec (A j)` are closed subschemes of
`Spec (A i) ×_K Spec (A j)`, hence affine of finite type over `K`. Both
projections `R ⇉ U` are étale, as base changes of the étale map `x`. So
`R ⇉ U` is an étale equivalence relation of schemes locally of finite type over
`K` whose map `R → U × U` is a closed immersion. Analytification preserves
these properties (Conrad–Temkin p.20, [Ber2, 3.3.11]), and Theorem 4.2.2 gives
the quotient `Y = 𝒰/ℛ`. By Definition 4.1.1 the map `𝒰 → Y` is an étale
surjection, so its restrictions `πᵢ` to the components are étale and jointly
surjective. The isomorphism `ℛ ≅ 𝒰 ×_Y 𝒰`, restricted to the components, says
that `Spec(B)ᵃⁿ = (Spec (A i) ×_X Spec (A j))ᵃⁿ` is the fibre product of `πᵢ`
and `πⱼ`. Here Berkovich `k`-analytic spaces are represented by the Library's
localized category and the affine analytification `Spec(A)ᵃⁿ` by
`AffineAnalytification.localized K P`.

## Provenance: derived

The proposition is a derived specialisation of Conrad–Temkin, Theorem 4.2.2 and
Definition 4.1.1, not a verbatim theorem of the source:
- the étale equivalence relation is the one attached to a family of étale
  affine charts of a separated algebraic space, as in the paragraph after
  Theorem 4.2.1 (p.20) and at the end of §4.3 (p.25), rather than an arbitrary
  analytic relation;
- the étale surjection `𝒰 → 𝒳` from the disjoint union is recorded through its
  components `πᵢ`, with surjectivity as joint surjectivity on underlying
  points, so no coproduct object is constructed or assumed;
- the isomorphism `ℛ ≅ 𝒰 ×_𝒳 𝒰` is recorded componentwise, as `IsPullback` in
  the localized category for every finite polynomial model `B` of the presheaf
  fibre product of two charts; each such square also contains the source's
  equality of the two composites `ℛ ⇉ 𝒰 → 𝒳`;
- separatedness, strictness and goodness of the quotient are omitted;
- only nontrivially normed fields are treated, because the Library's affine
  analytifications `AffineAnalytification.localized` are defined over them,
  while Conrad–Temkin allow a trivial absolute value in Theorem 4.2.2 (§1.5,
  p.4, and the parenthesis "allowing `|k^×| = {1}`" before Theorem 4.2.2).

## Place in the Library

The proposition is word for word the first premise of
`Langlands.Analytic.SpaceAnalytification.ExistenceReduction.SpaceAnalytificationExistenceFiveInputReductionStatement`
(module `Langlands.Geometry.Analytic.SpaceAnalytificationExistenceFiveInputReduction`),
so `SpaceAnalytificationChartQuotientStatement.{u}` can be passed as that
premise of `spaceAnalytificationExistenceFiveInputReduction` without
conversion. It provides only the quotient of the given charts: it says nothing
about test points of `X` that are not among the `x i`.
