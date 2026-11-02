import Langlands.CategoryTheory.Renard.JordanHolder

/-!
# Renard A.VI.3: the numerical length of a finite-length object

Source: Renard, *Représentations des groupes réductifs p-adiques*
(French edition dated 9 July 2026), Appendix A.VI.3, printed page 263 /
PDF page 269. The numerical length is defined only for an object equipped
with a proof that it admits a composition chain. The published Jordan–Hölder
theorem identifies it with the length of every such chain.
-/

set_option autoImplicit false

namespace Langlands.Renard

open CategoryTheory CategoryTheory.Limits

universe u v

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Renard's length of a finite-length object: the number of factors in any
composition chain. The finite-length proof supplies a witness; Jordan–Hölder
establishes its independence of the chain in `compositionLength_eq_of_chain`. -/
def compositionLength (X : C) (hX : IsFiniteLength X) : ℕ :=
  hX.choose

/-- A finite-length object admits a chain of its numerical length. -/
theorem hasCompositionChainOfLength_compositionLength (X : C) (hX : IsFiniteLength X) :
    HasCompositionChainOfLength X (compositionLength X hX) :=
  hX.choose_spec

/-- Every composition chain of a finite-length object has its numerical length. -/
theorem compositionLength_eq_of_chain {X : C} (hX : IsFiniteLength X) {n : ℕ}
    (c : CompositionChain X n) : compositionLength X hX = n := by
  obtain ⟨d⟩ := hasCompositionChainOfLength_compositionLength X hX
  exact (jordanHolder C X _ n d c).1

/-- The numerical length characterizes exactly the possible chain lengths. -/
theorem compositionLength_eq_iff {X : C} (hX : IsFiniteLength X) (n : ℕ) :
    compositionLength X hX = n ↔ HasCompositionChainOfLength X n := by
  constructor
  · intro h
    rw [← h]
    exact hasCompositionChainOfLength_compositionLength X hX
  · rintro ⟨c⟩
    exact compositionLength_eq_of_chain hX c

/-- The numerical length does not depend on the supplied finite-length proof. -/
theorem compositionLength_proof_irrel (X : C) (hX hX' : IsFiniteLength X) :
    compositionLength X hX = compositionLength X hX' :=
  rfl

/-- A finite-length object has length zero exactly when it is a zero object. -/
theorem compositionLength_eq_zero_iff {X : C} (hX : IsFiniteLength X) :
    compositionLength X hX = 0 ↔ IsZero X :=
  (compositionLength_eq_iff hX 0).trans (hasCompositionChainOfLength_zero_iff X)

end

end Langlands.Renard
