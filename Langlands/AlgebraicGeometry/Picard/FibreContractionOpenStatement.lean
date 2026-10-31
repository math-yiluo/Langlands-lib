import Langlands.AlgebraicGeometry.Picard.RelativePicardZero

/-! # Openness of the fibre-contraction locus of an abelian scheme -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- A morphism taking the unit section to one point contracts whole fibres
to that point over an open subset of the base. -/
def FibreContractionOpenStatement : Prop :=
  ∀ (Y Z : Scheme.{u}) (B : AbelianScheme Y) (Ψ : B.X.left ⟶ Z) (z₀ : Z),
    (∀ y : Y, Ψ (unitSection B y) = z₀) →
      IsOpen {y : Y | ∀ x : B.X.left, B.X.hom x = y → Ψ x = z₀}

end Langlands.AbelianScheme
