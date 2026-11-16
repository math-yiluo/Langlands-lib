import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import Mathlib.Tactic.FinCases

/-! # Rigidity of the numbered type-G2 Cartan matrix -/

namespace Langlands

/-- A numbering identifies every ordered entry with Mathlib's G2 matrix. -/
def IsTypeG2Numbering {ι : Type*} (M : Matrix ι ι ℤ) (e : ι ≃ Fin 2) : Prop :=
  ∀ a b, M a b = CartanMatrix.G₂ (e a) (e b)

namespace CartanG2Numbering

/-- The triple entry determines its two ordered vertices. -/
theorem eq_neg_three_iff (i j : Fin 2) :
    CartanMatrix.G₂ i j = -3 ↔ i = 0 ∧ j = 1 := by
  fin_cases i <;> fin_cases j <;> decide

/-- Every map preserving the actual G2 matrix fixes each vertex. -/
theorem rigid (f : Fin 2 → Fin 2)
    (hf : ∀ i j, CartanMatrix.G₂ (f i) (f j) = CartanMatrix.G₂ i j) :
    ∀ i, f i = i := by
  have h := (eq_neg_three_iff (f 0) (f 1)).mp
    ((hf 0 1).trans (by decide))
  intro i
  fin_cases i
  · exact h.1
  · exact h.2

/-- A type-G2 numbering of a fixed matrix is unique. -/
theorem unique {ι : Type*} {M : Matrix ι ι ℤ}
    (e f : ι ≃ Fin 2) (he : IsTypeG2Numbering M e) (hf : IsTypeG2Numbering M f) :
    e = f := by
  have hrigid := rigid (fun i => f (e.symm i)) (fun i j => by
    rw [← hf, he]
    simp)
  apply Equiv.ext
  intro a
  simpa using (hrigid (e a)).symm

end CartanG2Numbering

end Langlands
