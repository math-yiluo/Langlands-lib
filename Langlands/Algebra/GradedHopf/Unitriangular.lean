import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Factors of a unitriangular factorization lie in every subring containing the product -/

namespace Langlands.Algebra.GradedHopf

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Let `L` be lower and `U` upper unitriangular with respect to a function `τ : ι → ℕ`, in the
sense that an off-diagonal entry `L i j` (resp. `U i j`) vanishes unless `τ j < τ i`
(resp. `τ i < τ j`). If every entry of `L * U` lies in a subring `S`, then so does every entry
of `L` and of `U`. -/
theorem mem_of_mul_mem (S : Subring R) (τ : ι → ℕ) {L U : Matrix ι ι R}
    (hL1 : ∀ i, L i i = 1) (hU1 : ∀ i, U i i = 1)
    (hL : ∀ i j, L i j ≠ 0 → i = j ∨ τ j < τ i) (hU : ∀ i j, U i j ≠ 0 → i = j ∨ τ i < τ j)
    (hLU : ∀ i j, (L * U) i j ∈ S) : ∀ i j, L i j ∈ S ∧ U i j ∈ S := by
  have key : ∀ t, ∀ m, τ m = t → (∀ j, U m j ∈ S) ∧ (∀ j, L j m ∈ S) := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro m hm
      constructor
      · intro j
        have hterm : ∀ l ∈ Finset.univ.erase m, L m l * U l j ∈ S := by
          intro l hl
          by_cases h0 : L m l = 0
          · rw [h0, zero_mul]
            exact S.zero_mem
          rcases hL m l h0 with h | h
          · exact absurd h.symm (Finset.ne_of_mem_erase hl)
          · have := ih (τ l) (hm ▸ h) l rfl
            exact S.mul_mem (this.2 m) (this.1 j)
        have h := hLU m j
        rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ m), hL1, one_mul] at h
        have := S.sub_mem h (sum_mem hterm)
        rwa [add_sub_cancel_right] at this
      · intro j
        have hterm : ∀ l ∈ Finset.univ.erase m, L j l * U l m ∈ S := by
          intro l hl
          by_cases h0 : U l m = 0
          · rw [h0, mul_zero]
            exact S.zero_mem
          rcases hU l m h0 with h | h
          · exact absurd h (Finset.ne_of_mem_erase hl)
          · have := ih (τ l) (hm ▸ h) l rfl
            exact S.mul_mem (this.2 j) (this.1 m)
        have h := hLU j m
        rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ m), hU1, mul_one] at h
        have := S.sub_mem h (sum_mem hterm)
        rwa [add_sub_cancel_right] at this
  intro i j
  exact ⟨(key (τ j) j rfl).2 i, (key (τ i) i rfl).1 j⟩

end Langlands.Algebra.GradedHopf
