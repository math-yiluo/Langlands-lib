import Langlands.AbelianScheme.Tate.RationalPrimeIso
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Faithfulness target for the actual rational Tate action at one prime -/

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.Tate

universe u

/-- At every prime, the actual rational prime Tate map distinguishes rational
homomorphisms over algebraically closed characteristic-zero fields. -/
def FieldPrimeRationalFaithfulnessStatement : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    (A B : AbelianScheme (Spec (CommRingCat.of Ω))) (p : ℕ) [Fact p.Prime],
    Function.Injective
      (PrimeAdic.rationalHomMap (A := A) (B := B)
        (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) p)

namespace PrimeAdic

variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
  (A : AbelianScheme (Spec (CommRingCat.of Ω))) (p : ℕ) [Fact p.Prime]

/-- The same target makes the actual one-prime rational endomorphism action injective. -/
theorem rationalEndAction_injective_of_fieldFaithfulness
    (h : FieldPrimeRationalFaithfulnessStatement.{u}) :
    Function.Injective
      (rationalEndAction (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) p A) := by
  exact h Ω A A p

/-- Identity of the actual prime Tate operator detects identity of a rational endomorphism. -/
theorem rationalHomMap_eq_id_iff_of_fieldFaithfulness
    (h : FieldPrimeRationalFaithfulnessStatement.{u}) (f : Rationalization.End A) :
    rationalHomMap (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) p f = LinearMap.id ↔
      f = Rationalization.identity A := by
  constructor
  · intro hf
    apply h Ω A A p
    simpa only [rationalHomMap_identity] using hf
  · intro hf
    rw [hf, rationalHomMap_identity]

/-- Identity in the prime endomorphism algebra detects identity in the original rational algebra. -/
theorem rationalEndAction_eq_one_iff_of_fieldFaithfulness
    (h : FieldPrimeRationalFaithfulnessStatement.{u}) (f : Rationalization.End A) :
    rationalEndAction (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) p A f = 1 ↔ f = 1 := by
  constructor
  · intro hf
    apply rationalEndAction_injective_of_fieldFaithfulness A p h
    simpa only [map_one] using hf
  · intro hf
    rw [hf, map_one]

variable {A} {B : AbelianScheme (Spec (CommRingCat.of Ω))}

/-- Equality of the actual prime Tate equivalences determines the rational isomorphism. -/
theorem rationalIso_injective_of_fieldFaithfulness
    (h : FieldPrimeRationalFaithfulnessStatement.{u}) :
    Function.Injective
      (rationalIso (A := A) (B := B)
        (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) p) := by
  intro e f hef
  apply Iso.ext
  apply h Ω A B p
  apply LinearMap.ext
  intro x
  exact congrArg (fun g => g x) hef

/-- A rational self-isogeny is the identity if and only if its actual prime Tate equivalence is. -/
theorem rationalIso_eq_refl_iff_of_fieldFaithfulness
    (h : FieldPrimeRationalFaithfulnessStatement.{u})
    (e : Rationalization.of A ≅ Rationalization.of A) :
    rationalIso (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) p e =
        LinearEquiv.refl ℚ_[p] (Rational A (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) p) ↔
      e = Iso.refl (Rationalization.of A) := by
  constructor
  · intro he
    apply rationalIso_injective_of_fieldFaithfulness p h
    simpa only [rationalIso_refl] using he
  · intro he
    rw [he, rationalIso_refl]

end PrimeAdic
end Langlands.AbelianScheme.Tate
