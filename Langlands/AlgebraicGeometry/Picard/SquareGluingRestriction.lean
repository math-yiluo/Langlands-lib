import Langlands.AlgebraicGeometry.Picard.InfinitesimalGluing
import Langlands.AlgebraicGeometry.Picard.InfinitesimalAffineOpenSquare

/-! # Restriction of actual Picard square gluing data -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.SquareGluingRestriction

variable {Y₀ Y₁ Y₂ T₀ T₁ T₂ : Scheme.{u}}
  (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂)
  (ι₁ : T₀ ⟶ T₁) (ι₂ : T₀ ⟶ T₂)
  (g₁ : T₁ ⟶ Y₁) (g₂ : T₂ ⟶ Y₂) (g₀ : T₀ ⟶ Y₀)
  (k₁ : ι₁ ≫ g₁ = g₀ ≫ i₁) (k₂ : ι₂ ≫ g₂ = g₀ ≫ i₂)

/-- Pull back both legs and the specified overlap along two commuting faces.
The overlap uses the ordinary composition comparisons on both faces. -/
def pullback :
    PicardGroupoid.SquareGluingData i₁ i₂ ⥤
      PicardGroupoid.SquareGluingData ι₁ ι₂ :=
  Comma.map (PicardGroupoid.squarePullbackIso ι₁ g₀ g₁ i₁ k₁).hom
    (PicardGroupoid.squarePullbackIso ι₂ g₀ g₂ i₂ k₂).inv

variable {Y : Scheme.{u}} (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y)
  (w : i₁ ≫ j₁ = i₂ ≫ j₂) (U : Y.Opens)

/-- Restriction to the actual inverse-image square of an open subscheme. -/
def toOpen :
    PicardGroupoid.SquareGluingData i₁ i₂ ⥤
      PicardGroupoid.SquareGluingData
        (InfinitesimalAffineOpenSquare.leftRestriction i₁ j₁ U)
        (InfinitesimalAffineOpenSquare.rightRestriction i₁ i₂ j₁ j₂ w U) :=
  pullback i₁ i₂
    (InfinitesimalAffineOpenSquare.leftRestriction i₁ j₁ U)
    (InfinitesimalAffineOpenSquare.rightRestriction i₁ i₂ j₁ j₂ w U)
    (j₁ ⁻¹ᵁ U).ι (j₂ ⁻¹ᵁ U).ι ((i₁ ≫ j₁) ⁻¹ᵁ U).ι
    (InfinitesimalAffineOpenSquare.leftRestriction_ι i₁ j₁ U)
    (InfinitesimalAffineOpenSquare.rightRestriction_ι i₁ i₂ j₁ j₂ w U)

end Langlands.AlgebraicGeometry.Picard.SquareGluingRestriction
