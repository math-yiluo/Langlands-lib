import Langlands.AlgebraicGeometry.Modules.EulerCharacteristic

/-! # Additivity of actual cohomological Euler characteristics -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Euler characteristic is additive on an actual short exact sequence whose
three coefficient sheaves have finite cohomology. -/
def EulerCharacteristicAdditivityStatement : Prop :=
  ∀ (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of K)) (S : ShortComplex X.Modules),
    S.ShortExact →
      ∀ (h₁ : HasFiniteCohomology f S.X₁)
        (h₂ : HasFiniteCohomology f S.X₂)
        (h₃ : HasFiniteCohomology f S.X₃),
        eulerCharacteristic f S.X₂ h₂ =
          eulerCharacteristic f S.X₁ h₁ + eulerCharacteristic f S.X₃ h₃

end Langlands.AlgebraicGeometry.Modules.DerivedSections
