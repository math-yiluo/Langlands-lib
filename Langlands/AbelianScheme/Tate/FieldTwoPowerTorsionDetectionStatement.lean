import Langlands.AbelianScheme.Tate.Integral
import Langlands.AbelianScheme.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Detection of abelian-scheme homomorphisms by geometric 2-power torsion -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.Tate

universe u

/-- A homomorphism of abelian schemes over an algebraically closed field of
characteristic zero is zero if it kills all geometric 2-power torsion points. -/
def FieldTwoPowerTorsionDetectionStatement : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    (A B : AbelianScheme (Spec (CommRingCat.of Ω))) (f : A ⟶ B),
    (∀ n : ℕ, GroupScheme.Tate.levelMap
      (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) (AbelianScheme.groupHom f) (2 ^ n) = 0) →
    f = 0

end Langlands.AbelianScheme.Tate
