import Langlands.Global.RankinSelberg.ComplexLocalEqualTorusConvergence

/-! # From simple-root bounds to the complex equal-rank kernel bound -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexLocalConvergence

open Langlands.Archimedean

variable {r : ℕ}

local notation "I" => Fin (r + 1)
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "K" => unitaryCompact ℂ (r + 1)
local notation "row" => Langlands.RankinSelberg.lastRow

/-- The sum of the positive parts of the logarithms of the simple-root ratios. -/
def simpleRootLogSum (x : I → ℝ) : ℝ :=
  ∑ i : Fin r, max (x i.castSucc - x i.succ) 0

private theorem simpleRootLogSum_nonneg (x : I → ℝ) : 0 ≤ simpleRootLogSum x :=
  Finset.sum_nonneg fun _ _ => le_max_right _ _

private theorem coord_le_last_add_simpleRootLogSum (r : ℕ) (x : Fin (r + 1) → ℝ)
    (i : Fin (r + 1)) : x i ≤ x (Fin.last r) + simpleRootLogSum x := by
  induction r with
  | zero =>
    have hi : i = Fin.last 0 := by
      apply Fin.ext
      simpa only [Fin.val_last] using (show i.val = 0 by omega)
    simp [hi, simpleRootLogSum]
  | succ r ih =>
    let y : Fin (r + 1) → ℝ := fun j => x j.succ
    have htail (j : Fin (r + 1)) :
        x j.succ ≤ x (Fin.last (r + 1)) +
          ∑ l : Fin r, max (x l.succ.castSucc - x l.succ.succ) 0 := by
      simpa only [y, simpleRootLogSum, Fin.succ_last, Fin.succ_castSucc] using ih y j
    rw [simpleRootLogSum, Fin.sum_univ_succ]
    cases i using Fin.cases with
    | zero =>
      have hx := htail 0
      simp only [Fin.castSucc_zero]
      linarith [le_max_left (x 0 - x (Fin.succ (0 : Fin (r + 1)))) 0]
    | succ j =>
      apply (htail j).trans
      have h0 : 0 ≤ max (x (Fin.castSucc (0 : Fin (r + 1))) -
          x (Fin.succ (0 : Fin (r + 1)))) 0 := le_max_right _ _
      linarith

private theorem positiveLogSum_le (x : I → ℝ) :
    positiveLogSum x ≤ (r + 1) * (max (x (Fin.last r)) 0 + simpleRootLogSum x) := by
  unfold positiveLogSum
  calc
    _ ≤ ∑ _ : I, (max (x (Fin.last r)) 0 + simpleRootLogSum x) := by
      refine Finset.sum_le_sum fun i _ => max_le ?_ ?_
      · exact (coord_le_last_add_simpleRootLogSum r x i).trans
          (add_le_add_left (le_max_left _ _) _)
      · exact add_nonneg (le_max_right _ _) (simpleRootLogSum_nonneg x)
    _ = _ := by simp [nsmul_eq_mul, mul_add]

private theorem lastRow_expDiagonal_mul (x : I → ℝ) (k : K) :
    row (expDiagonal x * k.val) =
      (Real.exp (x (Fin.last r)) : ℂ) • row k.val := by
  funext j
  change ((expDiagonal x).val * k.val.val) (Fin.last r) j =
    (Real.exp (x (Fin.last r)) : ℂ) * k.val.val (Fin.last r) j
  rw [expDiagonal_val, Matrix.diagonal_mul]

private theorem lastRow_ne_zero (g : G) : row g ≠ 0 := by
  intro h
  have he := Langlands.RankinSelberg.lastRow_mul_eq_vecMul g g⁻¹
  rw [mul_inv_cancel, h, Matrix.zero_vecMul] at he
  have hx := congrFun he (Fin.last r)
  change (1 : Matrix I I ℂ) (Fin.last r) (Fin.last r) = 0 at hx
  rw [Matrix.one_apply_eq] at hx
  exact one_ne_zero hx

private theorem exists_lastRow_norm_pos_le : ∃ ε : ℝ, 0 < ε ∧ ∀ k : K, ε ≤ ‖row k.val‖ := by
  let := ComplexDuality.compactSpace_unitaryCompact (r + 1)
  have hc : Continuous (fun k : K => ‖row k.val‖) := by
    apply Continuous.norm
    exact continuous_pi fun j => (GeneralLinear.entry (R := ℂ) (Fin.last r) j).continuous.comp
      continuous_subtype_val
  obtain ⟨k, _, hmin⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty (α := K)) hc.continuousOn
  exact ⟨‖row k.val‖, norm_pos_iff.mpr (lastRow_ne_zero _), fun j => hmin (Set.mem_univ j)⟩

private theorem exists_schwartz_lastRow_bound (Φ : SchwartzMap (I → ℂ) ℂ) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : I → ℝ) (k : K),
      ‖Φ (row (expDiagonal x * k.val))‖ ≤ C * Real.exp (-L * max (x (Fin.last r)) 0) := by
  obtain ⟨ε, hε, hεk⟩ := exists_lastRow_norm_pos_le (r := r)
  obtain ⟨j, hj⟩ := exists_nat_ge L
  let c₀ := SchwartzMap.seminorm ℝ 0 0 Φ
  let c₁ := SchwartzMap.seminorm ℝ j 0 Φ / ε ^ j
  have hc₀ : 0 ≤ c₀ := apply_nonneg _ _
  have hc₁ : 0 ≤ c₁ := div_nonneg (apply_nonneg _ _) (pow_nonneg hε.le _)
  refine ⟨max c₀ c₁, hc₀.trans (le_max_left _ _), fun x k => ?_⟩
  let z := row (expDiagonal x * k.val)
  let t := x (Fin.last r)
  change ‖Φ z‖ ≤ max c₀ c₁ * Real.exp (-L * max t 0)
  rcases le_total 0 t with ht | ht
  · rw [max_eq_left ht]
    have hz : Real.exp t * ε ≤ ‖z‖ := by
      rw [show z = _ from lastRow_expDiagonal_mul x k, norm_smul, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hεk k) (Real.exp_nonneg _)
    have hp : 0 < ε ^ j * Real.exp ((j : ℝ) * t) := by positivity
    have hpow : ε ^ j * Real.exp ((j : ℝ) * t) ≤ ‖z‖ ^ j := by
      rw [Real.exp_nat_mul, ← mul_pow, mul_comm ε (Real.exp t)]
      exact pow_le_pow_left₀ (by positivity) hz _
    have hΦ : ‖Φ z‖ * (ε ^ j * Real.exp ((j : ℝ) * t)) ≤ SchwartzMap.seminorm ℝ j 0 Φ := by
      rw [mul_comm]
      exact (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans (Φ.norm_pow_mul_le_seminorm ℝ j z)
    have hC : ‖Φ z‖ ≤ c₁ * Real.exp (-(j : ℝ) * t) := by
      dsimp [c₁]
      rw [show -(j : ℝ) * t = -((j : ℝ) * t) by ring, Real.exp_neg,
        ← div_eq_mul_inv, ← div_mul_eq_div_div]
      exact (le_div_iff₀ hp).mpr hΦ
    exact hC.trans (mul_le_mul (le_max_right _ _)
      (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hj ht]))
      (Real.exp_nonneg _) (hc₀.trans (le_max_left _ _)))
  · rw [max_eq_right ht, mul_zero, Real.exp_zero, mul_one]
    exact (Φ.norm_le_seminorm ℝ z).trans (le_max_left _ _)

/-- The simple-root rapid-decrease estimate with a fixed growth exponent in the total
absolute logarithmic coordinates. -/
def HasSimpleRootLogBound (W : G → ℂ) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ L : ℝ, 0 ≤ L →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : I → ℝ) (k : K),
      ‖W (expDiagonal x * k.val)‖ ≤
        C * Real.exp (M * (positiveLogSum x + positiveLogSum (-x)) - L * simpleRootLogSum x)

/-- Jacquet's simple-root decay for the two coefficients and Schwartz decay of
the last-row test function supply the logarithmic kernel hypothesis. -/
theorem hasLogarithmicKernelBound_of_simpleRoots {W W' : G → ℂ}
    (hW : HasSimpleRootLogBound W) (hW' : HasSimpleRootLogBound W')
    (Φ : SchwartzMap (I → ℂ) ℂ) :
    HasLogarithmicKernelBound (fun g => W g * W' g * Φ (row g)) := by
  obtain ⟨M, hM, hW⟩ := hW
  obtain ⟨M', hM', hW'⟩ := hW'
  refine ⟨M + M', add_nonneg hM hM', fun L hL => ?_⟩
  let L' := (L + M + M') * (r + 1)
  have hL' : 0 ≤ L' := by dsimp [L']; positivity
  obtain ⟨C, hC, hW⟩ := hW L' hL'
  obtain ⟨C', hC', hW'⟩ := hW' 0 le_rfl
  obtain ⟨CΦ, hCΦ, hΦ⟩ := exists_schwartz_lastRow_bound Φ L'
  refine ⟨C * C' * CΦ, by positivity, fun x k => ?_⟩
  let P := positiveLogSum x
  let Q := positiveLogSum (-x)
  let S := simpleRootLogSum x
  let t := max (x (Fin.last r)) 0
  let g := expDiagonal x * k.val
  have hmajor : (L + M + M') * P ≤ L' * (t + S) := by
    simpa only [L', mul_assoc] using
      mul_le_mul_of_nonneg_left (positiveLogSum_le x) (by positivity : 0 ≤ L + M + M')
  have hT : (M + M') * (P + Q) - L' * (t + S) ≤ (M + M') * Q - L * P := by
    nlinarith
  change ‖W g * W' g * Φ (row g)‖ ≤ C * C' * CΦ * Real.exp ((M + M') * Q - L * P)
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (C * Real.exp (M * (P + Q) - L' * S)) * (C' * Real.exp (M' * (P + Q))) *
        (CΦ * Real.exp (-L' * t)) := by
      gcongr
      · exact hW x k
      · simpa only [zero_mul, sub_zero] using hW' x k
      · exact hΦ x k
    _ = (C * C' * CΦ) * Real.exp ((M + M') * (P + Q) - L' * (t + S)) := by
      rw [show (M + M') * (P + Q) - L' * (t + S) =
        (M * (P + Q) - L' * S) + M' * (P + Q) + (-L' * t) by ring]
      simp only [Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hT) (by positivity)

end Langlands.Global.RankinSelbergGlobal.ComplexLocalConvergence
