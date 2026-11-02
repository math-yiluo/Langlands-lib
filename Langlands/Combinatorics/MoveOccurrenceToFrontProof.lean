import Langlands.Combinatorics.MoveOccurrenceToFrontStatement

/-! # Adjacent transport of a specified original occurrence -/

namespace Langlands.Combinatorics

private def moveToPosition {r : ℕ} (i : Fin r) (k : ℕ) (hk : k ≤ i.val) :
    Equiv.Perm (Fin r) where
  toFun j := ⟨if j.val = k then i.val
    else if k < j.val ∧ j.val ≤ i.val then j.val - 1 else j.val, by
      have := i.isLt
      split_ifs <;> omega⟩
  invFun j := ⟨if j.val = i.val then k
    else if k ≤ j.val ∧ j.val < i.val then j.val + 1 else j.val, by
      have := i.isLt
      split_ifs <;> omega⟩
  left_inv j := by
    apply Fin.ext
    simp only
    split_ifs <;> omega
  right_inv j := by
    apply Fin.ext
    simp only
    split_ifs <;> omega

private theorem moveToPosition_self {r : ℕ} (i : Fin r) :
    moveToPosition i i.val le_rfl = 1 := by
  ext j
  change (if j.val = i.val then i.val
    else if i.val < j.val ∧ j.val ≤ i.val then j.val - 1 else j.val) = j.val
  split_ifs <;> omega

private theorem moveToPosition_step {r : ℕ} (i : Fin r) (k : ℕ) (hk : k < i.val) :
    moveToPosition i k hk.le =
      moveToPosition i (k + 1) hk *
        Equiv.swap ⟨k, by have := i.isLt; omega⟩
          ⟨k + 1, by have := i.isLt; omega⟩ := by
  apply Equiv.ext
  intro j
  rw [Equiv.Perm.mul_apply]
  by_cases hj : j = ⟨k, by have := i.isLt; omega⟩
  · subst j
    rw [Equiv.swap_apply_left]
    apply Fin.ext
    change (if k = k then i.val
      else if k < k ∧ k ≤ i.val then k - 1 else k) =
      (if k + 1 = k + 1 then i.val
        else if k + 1 < k + 1 ∧ k + 1 ≤ i.val then k + 1 - 1 else k + 1)
    simp
  · by_cases hj' : j = ⟨k + 1, by have := i.isLt; omega⟩
    · subst j
      rw [Equiv.swap_apply_right]
      apply Fin.ext
      change (if k + 1 = k then i.val
        else if k < k + 1 ∧ k + 1 ≤ i.val then k + 1 - 1 else k + 1) =
        (if k = k + 1 then i.val
          else if k + 1 < k ∧ k ≤ i.val then k - 1 else k)
      split_ifs <;> omega
    · rw [Equiv.swap_apply_of_ne_of_ne hj hj']
      apply Fin.ext
      change (if j.val = k then i.val
        else if k < j.val ∧ j.val ≤ i.val then j.val - 1 else j.val) =
        (if j.val = k + 1 then i.val
          else if k + 1 < j.val ∧ j.val ≤ i.val then j.val - 1 else j.val)
      simp only [Fin.ext_iff] at hj hj'
      split_ifs <;> omega

private theorem moveToPosition_zero {r : ℕ} (i : Fin r) :
    moveToPosition i 0 (Nat.zero_le _) = (Fin.cycleRange i).symm := by
  apply eq_inv_of_mul_eq_one_left
  ext j
  rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  by_cases hji : j ≤ i
  · have hval := Fin.coe_cycleRange_of_le hji
    change (if (Fin.cycleRange i j).val = 0 then i.val
      else if 0 < (Fin.cycleRange i j).val ∧ (Fin.cycleRange i j).val ≤ i.val
        then (Fin.cycleRange i j).val - 1 else (Fin.cycleRange i j).val) = j.val
    rw [hval]
    split_ifs <;> simp_all only [Fin.ext_iff, Fin.le_def] <;> omega
  · rw [Fin.cycleRange_of_gt (lt_of_not_ge hji)]
    change (if j.val = 0 then i.val
      else if 0 < j.val ∧ j.val ≤ i.val then j.val - 1 else j.val) = j.val
    simp only [Fin.le_def] at hji
    split_ifs <;> omega

/-- Move the chosen original occurrence left one adjacent position at a time. -/
theorem moveOccurrenceToFront : MoveOccurrenceToFront := by
  intro r P R hbase hswap i hcross
  have hall : ∀ (k : ℕ) (hk : k ≤ i.val), P (moveToPosition i k hk) := by
    apply Nat.decreasingInduction
    · intro k hk ih
      have hir := i.isLt
      have hleft : moveToPosition i (k + 1) hk ⟨k, by omega⟩ =
          ⟨k, by omega⟩ := by
        apply Fin.ext
        change (if k = k + 1 then i.val
          else if k + 1 < k ∧ k ≤ i.val then k - 1 else k) = k
        simp
      have hright : moveToPosition i (k + 1) hk ⟨k + 1, by omega⟩ = i := by
        apply Fin.ext
        change (if k + 1 = k + 1 then i.val
          else if k + 1 < k + 1 ∧ k + 1 ≤ i.val then k + 1 - 1 else k + 1) = i.val
        simp
      rw [moveToPosition_step i k hk]
      apply hswap _ k (by omega) _ ih
      rw [hleft, hright]
      exact hcross _ hk
    · rw [moveToPosition_self]
      exact hbase
  rw [← moveToPosition_zero]
  exact hall 0 (Nat.zero_le _)

end Langlands.Combinatorics
