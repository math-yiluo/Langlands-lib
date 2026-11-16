import Langlands.Geometry.Analytic.AnalyticImmersion
import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedMap
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Statement: affine analytification detects open and closed immersions -/

universe u v

namespace Langlands.Analytic.AffineAnalytification

open CategoryTheory SaturatedAtlasPresentation

/-- Let `K` be a complete nonarchimedean nontrivially normed field, let `A` and `B` be
commutative `K`-algebras with finite polynomial presentations `P` and `Q`, and let
`f : A → B` be a `K`-algebra map. Write `F : Spec(B)ᵃⁿ → Spec(A)ᵃⁿ` for the induced
morphism of analytic spaces. Then:
1. `f` is surjective if and only if `F` is a closed immersion;
2. `Spec(f) : Spec B → Spec A` is an open immersion of schemes if and only if `F` is an
   open immersion. -/
def AffineAnalytificationAnalyticImmersionStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A B : Type v) [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (f : A →ₐ[K] B),
    (Function.Surjective f ↔ closedImmersion (localizedHom K P Q f)) ∧
    (_root_.AlgebraicGeometry.IsOpenImmersion
        (_root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom f.toRingHom)) ↔
      openImmersion (localizedHom K P Q f))

end Langlands.Analytic.AffineAnalytification
