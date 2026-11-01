import Langlands.Algebra.RenardCommutativeDimensionNumericalContradictionStatement
import Mathlib.Tactic

namespace Langlands.Renard

/-- The exact real normalization and numerical contradiction ending Renard C.I. -/
theorem commutativeDimensionNumericalContradiction :
    CommutativeDimensionNumericalContradictionStatement := by
  intro l k hl hk
  dsimp only
  let ε : ℝ := 1 - (l : ℝ)
  let m : ℝ := (k : ℝ)
  let d : ℝ := (2 : ℝ) ^ ε
  let r : ℝ := 2 - d
  let x : ℝ := m ^ (-d)
  let D : ℝ := m ^ r
  let P : ℝ := m ^ (2 - (2 : ℝ) ^ (ε + 1))
  change 1 ≤ r ∧ 0 < 1 - x ∧ 1 - x < 1 ∧
    ((m - D / m) ^ r + P) / D = (1 - x) ^ r + x ∧
    (1 - x) ^ r ≤ 1 - x ∧ (m - D / m) ^ r + P ≤ D
  have hm1 : 1 < m := by dsimp [m]; exact_mod_cast (by omega : 1 < k)
  have hm : 0 < m := lt_trans zero_lt_one hm1
  have hε : ε ≤ 0 := by
    have hl' : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    dsimp [ε]
    linarith
  have hd : 0 < d := Real.rpow_pos_of_pos (by norm_num) _
  have hd1 : d ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hε
  have hr : 1 ≤ r := by dsimp [r]; linarith
  have hx : 0 < x := Real.rpow_pos_of_pos hm _
  have hx1 : x < 1 := Real.rpow_lt_one_of_one_lt_of_neg hm1 (neg_neg_of_pos hd)
  have hb : 0 < 1 - x := sub_pos.mpr hx1
  have hb1 : 1 - x < 1 := by linarith
  have hD : 0 < D := Real.rpow_pos_of_pos hm _
  have hDfactor : D = m * m * x := by
    change m ^ (2 - d) = m * m * m ^ (-d)
    rw [sub_eq_add_neg, Real.rpow_add hm]
    norm_num [Real.rpow_two, pow_two]
  have hbase : m - D / m = m * (1 - x) := by
    rw [hDfactor]
    field_simp
  have hdnext : (2 : ℝ) ^ (ε + 1) = 2 * d := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]
    change d * 2 = 2 * d
    ring
  have hP : P = D * x := by
    change m ^ (2 - (2 : ℝ) ^ (ε + 1)) =
      m ^ r * m ^ (-d)
    rw [hdnext, ← Real.rpow_add hm]
    congr 1
    dsimp [r]
    ring
  have hnorm : ((m - D / m) ^ r + P) / D =
      (1 - x) ^ r + x := by
    rw [hbase, Real.mul_rpow hm.le hb.le, hP]
    change (D * (1 - x) ^ r + D * x) / D = (1 - x) ^ r + x
    rw [← mul_add, mul_div_cancel_left₀ _ hD.ne']
  have hpower : (1 - x) ^ r ≤ 1 - x :=
    Real.rpow_le_self_of_le_one hb.le hb1.le hr
  refine ⟨hr, hb, hb1, hnorm, hpower, ?_⟩
  apply (div_le_one hD).mp
  rw [hnorm]
  linarith

end Langlands.Renard
