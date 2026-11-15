import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedMap

/-! # Statement: functoriality of affine analytification in the localized category -/

universe u v w x

namespace Langlands.Analytic.AffineAnalytification

open CategoryTheory

/-- Statement (affine case of the functoriality of analytification, Berkovich 1990, §3.4,
and Conrad–Temkin 2009, Theorem 2.2.3, as used in Conrad 2011, printed p.19, for the
Library's polynomial-locus model in the category of saturated presentations and in its
localized category): for a complete nonarchimedean nontrivially normed field `K`, finite
polynomial presentations `P`, `P'` of `A`, `Q` of `B` and `R` of `C`, and `K`-algebra maps
`f : A → B` and `g : B → C`,
1. the saturated morphism induced by the identity of `A` is the identity;
2. the saturated morphism induced by `g ∘ f` is the composite of those induced by `g` and
   by `f`;
3. the localized morphism induced by the identity of `A` is the identity;
4. the localized morphism induced by `g ∘ f` is the composite of those induced by `g` and
   by `f`;
5. the localized morphism induced by the identity of `A` from the analytification for `P'`
   to the analytification for `P` is an isomorphism. -/
def AffineAnalytificationLocalizedFunctorialityStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : Type v) [CommRing A] [Algebra K A] (B : Type w) [CommRing B] [Algebra K B]
    (C : Type x) [CommRing C] [Algebra K C]
    (P P' : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (R : FinitePolynomialPresentation K C) (f : A →ₐ[K] B) (g : B →ₐ[K] C),
    saturatedHom K P P (AlgHom.id K A) = 𝟙 (saturated K P) ∧
    saturatedHom K P R (g.comp f) = saturatedHom K Q R g ≫ saturatedHom K P Q f ∧
    localizedHom K P P (AlgHom.id K A) = 𝟙 (localized K P) ∧
    localizedHom K P R (g.comp f) = localizedHom K Q R g ≫ localizedHom K P Q f ∧
    IsIso (localizedHom K P P' (AlgHom.id K A))

end Langlands.Analytic.AffineAnalytification
