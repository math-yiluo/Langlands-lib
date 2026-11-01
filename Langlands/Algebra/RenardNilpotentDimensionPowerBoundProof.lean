import Langlands.Algebra.RenardNilpotentDimensionPowerBoundStatement
import Langlands.Algebra.RenardNilpotentDimensionBaseCasesProof
import Langlands.Algebra.RenardNilpotentDimensionFloorRecurrenceProof
import Langlands.Algebra.RenardCommutativeDimensionNumericalContradictionProof
import Mathlib.Algebra.Order.Floor.Semiring

namespace Langlands.Renard

/-- Renard C.I: the real-power bound on the actual canonical nilpotent maximum. -/
theorem nilpotentDimensionPowerBound :
    NilpotentDimensionPowerBoundStatement := by
  intro l
  induction l using Nat.strong_induction_on with
  | h l ihl =>
    intro k
    by_cases hlzero : l = 0
    · subst l
      rw [nilpotentDimensionBaseCases.{0}.2.2.2.2 k]
      split_ifs <;> norm_num
    have hl : 1 ≤ l := Nat.one_le_iff_ne_zero.mpr hlzero
    induction k using Nat.strong_induction_on with
    | h k ihk =>
      by_cases hkzero : k = 0
      · subst k
        rw [nilpotentDimensionBaseCases.{0}.2.1 l]
        simp only [Nat.cast_zero]
        apply Real.rpow_nonneg
        norm_num
      by_cases hkone : k = 1
      · subst k
        rw [nilpotentDimensionBaseCases.{0}.2.2.1 l]
        simp
      have hk : 2 ≤ k := by omega
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      let r : ℝ := 2 - Real.rpow 2 (1 - (l : ℝ))
      let D : ℝ := Real.rpow (k : ℝ) r
      let P : ℝ := Real.rpow (k : ℝ) (2 - Real.rpow 2 (1 - (l : ℝ) + 1))
      let q : ℝ := (k : ℝ) - (nilpotentGeneratedPhi l k : ℝ) / (k : ℝ)
      change (nilpotentGeneratedPhi l k : ℝ) ≤ D
      by_contra hbound
      have hstrict : D < (nilpotentGeneratedPhi l k : ℝ) := lt_of_not_ge hbound
      have hrec := nilpotentDimensionFloorRecurrence l k hl (by omega)
      change 0 ≤ q ∧ ⌊q⌋₊ < k ∧
        nilpotentGeneratedPhi l k ≤
          nilpotentGeneratedPhi l ⌊q⌋₊ + nilpotentGeneratedPhi (l - 1) k at hrec
      have hnumeric := commutativeDimensionNumericalContradiction l k hl hk
      change 1 ≤ r ∧ _ ∧ _ ∧ _ ∧ _ ∧
        Real.rpow ((k : ℝ) - D / (k : ℝ)) r + P ≤ D at hnumeric
      have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hnumeric.1
      have hsmall := ihk ⌊q⌋₊ hrec.2.1
      have hpred := ihl (l - 1) (by omega) k
      have hpredexp : 1 - ((l - 1 : ℕ) : ℝ) = 1 - (l : ℝ) + 1 := by
        rw [Nat.cast_sub hl]
        push_cast
        ring
      rw [hpredexp] at hpred
      change (nilpotentGeneratedPhi (l - 1) k : ℝ) ≤ P at hpred
      have hindex : (⌊q⌋₊ : ℝ) < (k : ℝ) - D / (k : ℝ) := by
        apply lt_of_le_of_lt (Nat.floor_le hrec.1)
        dsimp [q]
        exact sub_lt_sub_left ((div_lt_div_iff_of_pos_right hkpos).mpr hstrict) _
      have hpower : Real.rpow (⌊q⌋₊ : ℝ) r <
          Real.rpow ((k : ℝ) - D / (k : ℝ)) r :=
        Real.rpow_lt_rpow (by positivity) hindex hrpos
      have hrecR : (nilpotentGeneratedPhi l k : ℝ) ≤
          (nilpotentGeneratedPhi l ⌊q⌋₊ : ℝ) +
            (nilpotentGeneratedPhi (l - 1) k : ℝ) := by
        exact_mod_cast hrec.2.2
      have hsum : (nilpotentGeneratedPhi l k : ℝ) <
          Real.rpow ((k : ℝ) - D / (k : ℝ)) r + P := by
        exact lt_of_le_of_lt (hrecR.trans (add_le_add hsmall hpred))
          (by linarith [hpower])
      exact (not_lt_of_ge hnumeric.2.2.2.2.2) (hstrict.trans hsum)

end Langlands.Renard
