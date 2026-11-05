import Mathlib

/-! # Pointed etale local sections of smooth morphisms -/

universe u

open CategoryTheory

namespace Langlands.AlgebraicGeometry

open _root_.AlgebraicGeometry

/-- A prescribed residue-field point of a smooth scheme extends over a pointed
etale neighbourhood of the base point. -/
def SmoothPointedEtaleLocalSectionsStatement : Prop :=
  ∀ (X S : Scheme.{u}) (f : X ⟶ S), Smooth f →
    ∀ (s : S) (x₀ : Spec (S.residueField s) ⟶ X),
      x₀ ≫ f = S.fromSpecResidueField s →
      ∃ (U : Scheme.{u}) (p : U ⟶ S) (b : Spec (S.residueField s) ⟶ U) (a : U ⟶ X),
        Etale p ∧ b ≫ p = S.fromSpecResidueField s ∧ a ≫ f = p ∧ b ≫ a = x₀

end Langlands.AlgebraicGeometry
