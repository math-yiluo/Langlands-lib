# Statement: functoriality of affine analytification in the localized category

`AffineAnalytificationLocalizedFunctorialityStatement` states that the
morphisms `saturatedHom` and `localizedHom` of `AffineAnalytificationLocalizedMap`
respect identities and composites. It also states that the morphism induced by
the identity between the analytifications for two presentations of the same
algebra is an isomorphism in the localized category. It is a `Prop`-valued
definition; this module supplies no proof.

## Provenance

Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*
(1990), Theorem 3.4.1, printed p.63/PDF p.77, defines the analytification
`X^an` of a scheme `X` locally of finite type over `k` as the `k`-analytic space
representing `𝒵 ↦ Hom_k(𝒵, X)`. By the Yoneda lemma, a standard consequence
that Berkovich does not spell out, a representing object is unique up to unique
isomorphism and functorial in `X`. So `X ↦ X^an` respects identities and
composites and does not depend on choices. Proposition 3.4.6, printed p.65/PDF
p.79, uses the resulting morphism `g^an`. The registered source is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256 `9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.

Berkovich, *Étale cohomology for non-Archimedean analytic spaces* (1993),
Definition 1.2.7 and Proposition 1.2.8, printed p.18/PDF p.15, define strong
morphisms and their unique extension to maximal atlases. Definition 1.2.9,
printed p.19/PDF p.16, defines quasi-isomorphisms, and printed p.20/PDF p.17
defines the category of `K`-analytic spaces as the category of fractions with
respect to them. The Library's `SaturatedAtlasPresentation` category and its
`LocalizedCategory` implement these notions. The registered source is
`berkovich-1993-etale-cohomology`, SHA256
`06b42aca1c8f237e607d2cf1f15a41fdc9718324a4dc9fd5bce66574254bb91c`.

Conrad–Temkin, *Non-archimedean analytification of algebraic spaces* (2009),
Theorem 2.2.3 and its proof, printed pp.7–8, prove for algebraic spaces that
`f^an` does not depend on the étale charts or the lift of `f`, and that the
construction is compatible with composition. The registered source is
`conrad-temkin-2009-nonarchimedean-analytification`, SHA256
`ecfb9dad9c7e27ec36e3a40111ea140fc3bf2589f41b58f97e036e4e2ce6394e`.
Conrad, *Weil and Grothendieck approaches to adelic points* (2011), printed
p.19, final paragraph of the proof of Proposition 5.11(3), relies on this
functorial analytification. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The sources prove functoriality through universal properties. The statement
here is a derived formulation for the Library's explicit polynomial-locus model
in the category of saturated presentations and its localized category. It is
the affine content of the source functoriality in this model. Conjunct 5
expresses independence of the presentation.

## Hypotheses

The field `K : Type u` is nontrivially normed, ultrametric and complete. The
algebras `A : Type v`, `B : Type w` and `C : Type x` are commutative
`K`-algebras. `P` and `P'` are finite polynomial presentations of `A`, `Q` of
`B` and `R` of `C`. The maps `f : A →ₐ[K] B` and `g : B →ₐ[K] C` are arbitrary
`K`-algebra maps. No injectivity, surjectivity, reducedness or nonemptiness is
assumed.

`saturatedHom K P Q f : saturated K Q ⟶ saturated K P` is the published
saturation extension of the strong atlas map induced by `f`.
`localizedHom K P Q f : localized K Q ⟶ localized K P` is its image under
`localizationFunctor`; it is the morphism `Spec(B)ᵃⁿ → Spec(A)ᵃⁿ`. Composition
`≫` in the category of saturated presentations is the Library's
`StrongHom.saturatedComp`; composition in the localized category is
composition in Mathlib's localization of that category.

## The statement

For all such data, the following five assertions hold.

1. `saturatedHom K P P (AlgHom.id K A) = 𝟙 (saturated K P)`.
2. `saturatedHom K P R (g.comp f) =
   saturatedHom K Q R g ≫ saturatedHom K P Q f`. This is the morphism from the
   saturation for `R` through that for `Q` to that for `P`.
3. `localizedHom K P P (AlgHom.id K A) = 𝟙 (localized K P)`.
4. `localizedHom K P R (g.comp f) =
   localizedHom K Q R g ≫ localizedHom K P Q f`.
5. `IsIso (localizedHom K P P' (AlgHom.id K A))`: the morphism from the
   analytification for `P'` to the analytification for `P` induced by the
   identity of `A` is an isomorphism in the localized category.

Equalities 1 and 2 are equalities of the Library's `StrongHom` structures of the
saturated presentations: equal continuous base maps and equal bounded pullbacks
for every admissible pair of full local affinoid domains.

## Truth sketch

This is not a Lean proof. Assertions 1 and 2 reduce, by the Library's
`StrongHom.ext_on_original` and `saturationExtension_pullback_original`, to the
original charts. There they are the identity and composition equalities of the
published `AffineAnalytificationFunctorialityStatement`. Assertions 3 and 4
follow from 1 and 2 because `localizationFunctor` is a functor. For assertion 5,
assertions 3 and 4 applied to `P`, `P'`, `P` and to `P'`, `P`, `P'` with both
maps the identity of `A` give both inverse composites. Since `AlgHom.id`
composed with itself is `AlgHom.id`, the inverse is
`localizedHom K P' P (AlgHom.id K A)`. A proof can establish assertion 4 as a
universe-polymorphic lemma and apply it with all three algebras equal to `A`.

## Scope

The statement does not cover nonaffine schemes, the gluing of affine pieces,
open or closed immersions, rational points, the center map, fibre products,
extension of the ground field, or the universal property of the
analytification.
