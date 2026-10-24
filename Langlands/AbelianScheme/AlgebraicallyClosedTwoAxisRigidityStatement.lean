import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Two-axis rigidity over an algebraically closed field -/

universe u

open CategoryTheory AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory

namespace Langlands.AbelianScheme

/-- A morphism from a proper integral square, constant with the same value on both
pointed axes, is constant. The target is separated and locally of finite type. -/
def AlgebraicallyClosedTwoAxisRigidity : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (A H : Over (Spec (CommRingCat.of K))),
    IsProper A.hom →
    IsIntegral (A ⊗ A).left →
    IsSeparated H.hom →
    LocallyOfFiniteType H.hom →
    ∀ (a : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A)
      (b : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ H)
      (g : A ⊗ A ⟶ H),
      (a ▷ A) ≫ g = toUnit (𝟙_ (Over (Spec (CommRingCat.of K))) ⊗ A) ≫ b →
      (A ◁ a) ≫ g = toUnit (A ⊗ 𝟙_ (Over (Spec (CommRingCat.of K)))) ≫ b →
      g = toUnit (A ⊗ A) ≫ b

end Langlands.AbelianScheme
