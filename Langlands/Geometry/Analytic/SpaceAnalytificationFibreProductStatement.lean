import Langlands.Geometry.Analytic.SpaceAnalytification
import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry

/-!
# Analytification of algebraic spaces preserves fibre products

The analytifications of a pullback square of separated algebraic spaces locally of finite
type over `Spec K`, joined by the morphisms compatible with affine test points, form a
pullback square of analytic spaces.
-/

universe u

namespace Langlands.Analytic.SpaceAnalytification

open CategoryTheory SaturatedAtlasPresentation
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Let `W` be a fibre product of `f₁ : X₁ ⟶ Z` and `f₂ : X₂ ⟶ Z`, with projections `π₁` and
`π₂`, where `X₁`, `X₂` and `Z` are separated and locally of finite type over `Spec K`. Given
analytifications of `W`, `X₁`, `X₂` and `Z`, and morphisms between them compatible with the
maps attached to affine test points, the resulting square of analytic spaces is a pullback. -/
def SpaceAnalytificationFibreProductStatement : Prop :=
  ∀ (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (W X₁ X₂ Z : AlgebraicSpace (Spec (CommRingCat.of K)))
    (π₁ : W ⟶ X₁) (π₂ : W ⟶ X₂) (f₁ : X₁ ⟶ Z) (f₂ : X₂ ⟶ Z),
    IsPullback π₁ π₂ f₁ f₂ →
    IsSeparated X₁ → LocallyOfFiniteTypeOverBase X₁ →
    IsSeparated X₂ → LocallyOfFiniteTypeOverBase X₂ →
    IsSeparated Z → LocallyOfFiniteTypeOverBase Z →
    ∀ (V Y₁ Y₂ T : LocalizedCategory.{u, u, u} (K := K)) (q : PointFamily K W V)
      (p₁ : PointFamily K X₁ Y₁) (p₂ : PointFamily K X₂ Y₂) (r : PointFamily K Z T),
      IsAnalytification K W V q → IsAnalytification K X₁ Y₁ p₁ →
      IsAnalytification K X₂ Y₂ p₂ → IsAnalytification K Z T r →
      ∀ (Φ₁ : V ⟶ Y₁) (Φ₂ : V ⟶ Y₂) (F₁ : Y₁ ⟶ T) (F₂ : Y₂ ⟶ T),
        (∀ (A : Type u) [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)
          (x : RingPoints K W A), q A P x ≫ Φ₁ = p₁ A P (RingPoints.map π₁ x)) →
        (∀ (A : Type u) [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)
          (x : RingPoints K W A), q A P x ≫ Φ₂ = p₂ A P (RingPoints.map π₂ x)) →
        (∀ (A : Type u) [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)
          (x : RingPoints K X₁ A), p₁ A P x ≫ F₁ = r A P (RingPoints.map f₁ x)) →
        (∀ (A : Type u) [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)
          (x : RingPoints K X₂ A), p₂ A P x ≫ F₂ = r A P (RingPoints.map f₂ x)) →
        IsPullback Φ₁ Φ₂ F₁ F₂

end Langlands.Analytic.SpaceAnalytification
