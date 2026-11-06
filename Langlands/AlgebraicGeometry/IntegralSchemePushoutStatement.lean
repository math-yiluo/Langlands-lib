import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! # Scheme pushouts along closed immersions and integral morphisms -/

open CategoryTheory AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry

/-- Selected conclusions of Stacks, Tag 0E25, with the fibre-neighborhood
hypothesis of Tag 0ECI retained explicitly. -/
def IntegralSchemePushoutStatement : Prop :=
  ∀ (X Y Z : Scheme.{u}) (i : Z ⟶ X) (j : Z ⟶ Y),
    IsClosedImmersion i →
      IsIntegralHom j →
        (∀ y : Y, ∃ U : X.Opens,
          IsAffineOpen U ∧ ∀ z : Z, j z = y → i z ∈ U) →
        ∃ (P : Scheme.{u}) (a : X ⟶ P) (b : Y ⟶ P),
          IsPushout i j a b ∧ IsPullback i j a b ∧
            IsIntegralHom a ∧ IsClosedImmersion b

end Langlands.AlgebraicGeometry
