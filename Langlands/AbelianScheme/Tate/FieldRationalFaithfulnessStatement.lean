import Langlands.AbelianScheme.Tate.Rational
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Faithfulness target for the actual full rational Tate construction -/

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.Tate

universe u

/-- Over an algebraically closed characteristic-zero field, the full rational
Tate map distinguishes actual rational homomorphisms of abelian schemes. -/
def FieldRationalFaithfulnessStatement : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    (A B : AbelianScheme (Spec (CommRingCat.of Ω))),
    Function.Injective
      (rationalHomMap (A := A) (B := B)
        (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) (fun _ => True))

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
  (A : AbelianScheme (Spec (CommRingCat.of Ω)))

/-- The same hypothesis makes the constructed rational endomorphism action
injective; no new endomorphism representation is chosen. -/
theorem rationalEndAction_injective_of_fieldFaithfulness
    (h : FieldRationalFaithfulnessStatement.{u}) :
    Function.Injective
      (rationalEndAction A (Over.mk (𝟙 (Spec (CommRingCat.of Ω))))
        (fun _ => True)) := by
  exact h Ω A A

variable {A} {B : AbelianScheme (Spec (CommRingCat.of Ω))}

/-- Equality of the actual induced full rational Tate equivalences determines
the original rational isomorphism, conditional on the named faithfulness target. -/
theorem rationalIso_injective_of_fieldFaithfulness
    (h : FieldRationalFaithfulnessStatement.{u}) :
    Function.Injective
      (rationalIso (A := A) (B := B)
        (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) (fun _ => True)) := by
  intro e f hef
  apply Iso.ext
  apply h Ω A B
  apply LinearMap.ext
  intro x
  exact congrArg (fun g => g x) hef

end Langlands.AbelianScheme.Tate
