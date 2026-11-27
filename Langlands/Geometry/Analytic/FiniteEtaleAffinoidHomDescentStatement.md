# Descent of analytic morphisms along finite étale covers of affinoid spaces

This module contains only the Prop-valued definition
`Langlands.Analytic.SaturatedAtlasPresentation.FiniteEtaleAffinoidHomDescentStatement`:
a morphism from the spectrum of `B` to an arbitrary analytic space `T` that satisfies the
kernel-pair condition for a finite étale, spectrum-surjective map of affinoid spaces
`M(B) → M(A)` factors through `M(A)`. The file states the proposition and does not prove
it.

## Exact statement

`FiniteEtaleAffinoidHomDescentStatement.{u, v} : Prop` asserts the following.

Let `K : Type u` be a field with `NormedField K`, `IsUltrametricDist K` and
`CompleteSpace K`. Let `A B : PresentedAffinoidAlgebra K` with
`Small.{v} (BanachSpectrum A)` and `Small.{v} (BanachSpectrum B)`, and let
`f : BoundedAlgHom K A B` satisfy

1. `f.IsFiniteBanach`,
2. `f.AlgebraicallyFiniteEtale`,
3. `Function.Surjective (BanachSpectrum.comap f.toBoundedRingHom)`.

Write `M(A)` and `M(B)` for
`localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, v} A)` and
`localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, v} B)`, and `M(f) : M(B) ⟶ M(A)`
for `localizationFunctor.map (SmallAffinoidSpectrum.map f)`. Then for every
`T : LocalizedCategory.{u, v, v} (K := K)` and every `g : M(B) ⟶ T` such that

```text
∀ (Z : LocalizedCategory.{u, v, v} (K := K)) (a b : Z ⟶ M(B)),
  a ≫ M(f) = b ≫ M(f) → a ≫ g = b ≫ g
```

there exists `h : M(A) ⟶ T` with `M(f) ≫ h = g`.

## The hypotheses

- **The field.** Only `NormedField K` is assumed, with the ultrametric inequality and
  completeness; the norm may be trivial. These are the hypotheses under which the Library
  defines `LocalizedCategory`, `localizationFunctor` and `SmallAffinoidSpectrum.saturated`.
- **Universes.** The field universe `u` and the universe `v` of the analytic spaces are
  independent. `LocalizedCategory.{u, v, v}` is the localization at quasi-isomorphisms of
  saturated affinoid atlas presentations whose underlying spaces and chart index types lie in
  `v`. The instances `Small.{v} (BanachSpectrum A)` and `Small.{v} (BanachSpectrum B)` let
  `SmallAffinoidSpectrum.saturated` realize the two spectra in this universe.
- **Affinoid algebras.** A `PresentedAffinoidAlgebra K` is a quotient of a generalized Tate
  algebra of positive polyradius by a closed ideal, that is, a `K`-affinoid algebra in
  Berkovich's sense, not necessarily strict. `BanachSpectrum` is its spectrum of bounded
  multiplicative seminorms. `SmallAffinoidSpectrum.map f : saturated B ⟶ saturated A` is the
  morphism of saturated presentations given by `f`. Its point map is
  `BanachSpectrum.comap f.toBoundedRingHom`, transported by the canonical homeomorphisms
  (`SmallAffinoidSpectrum.map_spectrumHomeomorph`).
- **`f.IsFiniteBanach`** (`Langlands.Analytic.BoundedAlgHom.IsFiniteBanach`): `B` is a finite
  Banach `A`-algebra through `f`. Some finite coefficient map from a finite free `A`-module with
  the maximum norm onto `B` is an admissible epimorphism. Thus `M(B) → M(A)` is a finite
  morphism of `K`-affinoid spaces.
- **`f.AlgebraicallyFiniteEtale`** (`Langlands.Analytic.BoundedAlgHom.AlgebraicallyFiniteEtale`):
  the underlying ring map `A → B` is finite and étale. Together with the previous hypothesis,
  `M(B) → M(A)` is a finite étale morphism of `K`-affinoid spaces.
- **Spectrum surjectivity.** The map `M(B) → M(A)` of spectra is surjective. Since an étale
  ring map is flat, `f` is then faithfully flat
  (`Langlands.Analytic.SmallAffinoidSpectrum.faithfullyFlat_of_flat_of_spectrum_surjective`),
  so `M(B) → M(A)` is one of the finite faithfully flat morphisms of `K`-affinoid spaces in
  Berkovich's Lemma 4.1.1(2).
- **The target `T`** is an arbitrary object of `LocalizedCategory.{u, v, v} (K := K)`. It is
  not assumed to be affinoid, good or étale over anything, and `g` and `h` are arbitrary
  morphisms of the localized category, not morphisms over a base.
- **The hypothesis on `g` is the kernel-pair condition.** It says that `g` coequalizes every
  pair of morphisms that `M(f)` identifies. Equivalently, `g` takes the same value on the two
  projections `M(B) ×_{M(A)} M(B) ⇉ M(B)` of the kernel pair of `M(f)`. The Library realizes
  this fibre product by the finite Banach pushout. The completed pushout `B ⊗̂_A B` has a
  `v`-small spectrum by
  `Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidPushout.small_spectrum_of_finiteBanachPushout`
  applied to `finiteBanachPushout` and `f.IsFiniteBanach`. Its two projections
  `localizationFunctor.map (SmallAffinoidSpectrum.finitePushoutFst f f finiteBanachPushout hf)`
  and the corresponding `finitePushoutSnd` form a pullback of `M(f)` along itself in the
  localized category (`Langlands.Analytic.SmallAffinoidSpectrum.pushout_localized_isPullback`).
  Hence the hypothesis on `g` is equivalent to the equality of the two composites
  `M(B) ×_{M(A)} M(B) ⇉ M(B) → T`. If the two composites agree, a pair `a, b` with
  `a ≫ M(f) = b ≫ M(f)` factors through the two projections by the pullback property, so
  `a ≫ g = b ≫ g`. Conversely, the two projections are such a pair by
  `SmallAffinoidSpectrum.finitePushout_condition`. The statement uses the intrinsic form, which
  names no chosen fibre product.

## What the statement does not include

- **Uniqueness of `h`** is not part of the statement. It follows from
  `Langlands.Analytic.SaturatedAtlasPresentation.etaleCoverHomExt`, applied to the
  one-member family `M(f)`, once `M(f)` is known to be étale. The covering condition of
  `etaleCoverHomExt` is then the spectrum surjectivity above, by
  `localizedSpaceFunctor_map` and `SmallAffinoidSpectrum.map_spectrumHomeomorph`. For a
  finite Banach, algebraically finite étale `f`, étaleness of `M(f)` follows from
  `Langlands.Analytic.SmallAffinoidSpectrum.map_etale_of_finite_pointwiseEtale` with
  `finiteBanachPushout`, `finiteTensorComparison` and
  `Langlands.Analytic.BoundedAlgHom.AlgebraicallyFiniteEtale.isEtaleAtPoint`.
- No analytic fibre product of arbitrary analytic spaces is stated or assumed. The kernel-pair
  condition quantifies over all test morphisms and does not mention a fibre product.
- No image theorem is stated: the statement does not assert that the image of an affinoid
  or quasi-compact analytic domain under a finite étale map is a finite union of affinoid
  domains, which is Conrad–Temkin's Theorem 4.1.2.
- No descent of analytic domains (Conrad–Temkin, Example 4.1.3) is stated.

## Original sources

Berkovich, *Étale cohomology for non-Archimedean analytic spaces*, Publ. Math. IHÉS 78
(1993), registered as `berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`
(printed page = PDF page + 3):

- §1.2, printed p.14 (PDF p.11): the ground field `k` is a fixed non-Archimedean field, and
  the valuation on `k` is not assumed to be nontrivial.
- §4.1, printed p.82 (PDF p.79): the big flat quasifinite site of `X` and Lemma 4.1.1. Its
  condition (2) asks, for every finite faithfully flat morphism of `k`-affinoid spaces
  `Z → Y` over `X`, that the sequence `F(Y) → F(Z) ⇉ F(Z ×_Y Z)` be exact.
- printed p.83 (PDF p.80): the proof of Lemma 4.1.1. It reduces a covering to one by finite
  morphisms `V_ij → φ_i(V_ij)`, then to a single finite faithfully flat morphism `Z → Y`,
  and through quasinets of affinoid domains to the `k`-affinoid case of condition (2).
  Proposition 4.1.3 on the same page: a presheaf representable by a `k`-analytic space good
  over `X` is a sheaf on the big flat quasifinite site. Its proof shows uniqueness of the
  descended morphism without the goodness assumption. It constructs the descended morphism
  locally for good `X'`, by choosing an affinoid neighbourhood of `g(z)` in `X'`.
- printed p.84 (PDF p.81): the end of the proof of Proposition 4.1.3, and Remark 4.1.5. The
  remark says that Proposition 4.1.3 should hold without goodness. For this it would suffice
  that for a finite étale morphism of `k`-affinoid spaces `φ : Y → X` and an affinoid domain
  `V ⊆ Y`, the image `φ(V)` be a finite union of affinoid domains in `X`.

Conrad–Temkin, *Non-archimedean analytification of algebraic spaces*, J. Algebraic Geom. 18
(2009), registered as `conrad-temkin-2009-nonarchimedean-analytification`, SHA256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`
(printed page = PDF page):

- p.18, the paragraph before Theorem 4.1.2. Representable functors on the category of
  `k`-analytic spaces are étale sheaves within good and within strictly `k`-analytic
  spaces by [Ber2, 4.1.5], and in general once Theorem 4.1.2 is proved.
- Theorem 4.1.2, pp.18–19: for a finite étale map `f : X' → X` of `k`-analytic spaces and a
  quasi-compact `k`-analytic subdomain `V' ⊆ X'`, the image `f(V')` is a finite union of
  `k`-affinoid subdomains of `X`. A nontrivial absolute value is not a hypothesis. The proof
  reduces to the affinoid case and checks the final isomorphism after an analytic extension
  of the base field, so that `|k^×| ≠ {1}`.
- p.19, the paragraph after Example 4.1.3: by Theorem 4.1.2, a quotient of an étale
  equivalence relation represents the quotient sheaf on the étale site of the category of
  `k`-analytic spaces. This uses the sheaf property of representable functors.

## Provenance: derived

The proposition is condition (2) of Berkovich's Lemma 4.1.1 for the presheaf
`Y ↦ Hom(Y, T)` represented by `T`, restricted to finite étale maps of affinoid spaces instead
of all finite faithfully flat ones, and only its existence half. Take `Y = M(A)` and
`Z = M(B)`. Then `F(Y) → F(Z)` is `h ↦ M(f) ≫ h`, and exactness at `F(Z)` asks that every
`g` with equal composites on the two projections of `Z ×_Y Z` comes from some `h`. The
hypothesis on `g` is this equality (see the kernel-pair condition above). The base `X` of
Lemma 4.1.1 is taken to be the point `M(K)`, so that morphisms over `X` are all morphisms of
`K`-analytic spaces.

The sources give this for the following reasons. For `T` good, the proof of Berkovich's
Proposition 4.1.3 establishes condition (2) for every finite faithfully flat morphism of
affinoid spaces, in particular for the finite étale surjective ones here. For arbitrary `T`,
Remark 4.1.5 states that Proposition 4.1.3 should hold without goodness, and that the image
property for finite étale morphisms of `k`-affinoid spaces would suffice. Conrad–Temkin's
Theorem 4.1.2 proves this property, with no restriction on the absolute value of the ground
field, and the paragraph before it draws the conclusion that representable functors are
étale sheaves in general. This is why the statement is restricted to finite étale maps. For
an étale covering, the finite morphisms `V_ij → φ_i(V_ij)` in the proof of Lemma 4.1.1 are
restrictions of étale morphisms, hence finite étale, and for finite étale maps the sources
cover every target `T`. Berkovich does not assume a nontrivial valuation (§1.2), which
matches the trivially normed fields allowed here.

## Place in the Library

In Berkovich's proof of Lemma 4.1.1, the sheaf property for a covering is reduced to
condition (2) for single finite morphisms of affinoid spaces. In the Library the étale-site
form of the sheaf property for represented presheaves is
`Langlands.Analytic.SaturatedAtlasPresentation.EtaleHomSheafStatement`. The present
proposition is the affinoid finite étale existence step of that reduction. Uniqueness of
descended morphisms is the separate `etaleCoverHomExt` (see above).

`Langlands.Analytic.SmallAffinoidSpectrum.FiniteAffinoidLocalizedHomDescentStatement`, proved
by `finiteAffinoidLocalizedHomDescent`, is a related affinoid case. Its target is a small
affinoid spectrum, its field is nontrivially normed, its map is finite Banach, flat and
spectrum-surjective (not necessarily étale), its hypothesis is stated on the finite Banach
pushout projections, and its conclusion includes uniqueness. The present statement allows an
arbitrary target and trivially normed fields, and asks only for existence.
