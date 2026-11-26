import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Exponential

/-! # Small exponential bounds from a boundary near the center -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Analysis.SeveralComplex

open Metric Set

/-- A family of entire functions with a common exponential bound on a fixed disk and
arbitrarily small exponential bounds on vertical segments just to the right of the origin
has an arbitrarily small exponential bound at the origin. -/
theorem smallExponentialAtZero_of_rightBoundary {ι : Type*} {F : ℂ → ι → ℂ} {S : ι → ℝ}
    (hS : ∀ i, 0 ≤ S i) (hF : ∀ i, Differentiable ℂ (fun z => F z i))
    {C M D : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hDisk : ∀ z ∈ closedBall (0 : ℂ) 2, ∀ i, ‖F z i‖ ≤ C * Real.exp (M * S i))
    (hLine : ∀ δ ∈ Ioo (0 : ℝ) 1, ∃ A : ℝ, 0 ≤ A ∧
      ∀ z : ℂ, z.re = δ → |z.im| ≤ 1 → ∀ i, ‖F z i‖ ≤ A * Real.exp (D * δ * S i)) :
    ∀ ε > 0, ∃ B : ℝ, 0 ≤ B ∧ ∀ i, ‖F 0 i‖ ≤ B * Real.exp (ε * S i) := by
  intro ε hε
  let δ := min (1 / 2) (ε / (1 + D + 2 * M))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδ₁ : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hδε : (D + 2 * M) * δ ≤ ε := by
    have h := (le_div_iff₀ (show 0 < 1 + D + 2 * M by positivity)).mp
      (min_le_right (1 / 2) (ε / (1 + D + 2 * M)))
    nlinarith
  obtain ⟨A, hA, hAbound⟩ := hLine δ ⟨hδ, hδ₁⟩
  let U : Set ℂ := {z | (δ - 1 ≤ z.re ∧ z.re ≤ δ) ∧ (-1 ≤ z.im ∧ z.im ≤ 1)}
  have hUclosed : IsClosed U :=
    ((isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_le Complex.continuous_re continuous_const)).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const))
  have hUdisk : U ⊆ closedBall (0 : ℂ) 2 := by
    intro z hz
    obtain ⟨⟨hl, hr⟩, hb, ht⟩ := hz
    have hRe : |z.re| ≤ 1 := abs_le.mpr ⟨by linarith, hr.trans hδ₁.le⟩
    have hIm : |z.im| ≤ 1 := abs_le.mpr ⟨hb, ht⟩
    exact mem_closedBall_zero_iff.mpr ((Complex.norm_le_abs_re_add_abs_im z).trans (by linarith))
  have hUbounded : Bornology.IsBounded U := isBounded_closedBall.subset hUdisk
  have h₀U : (0 : ℂ) ∈ U := by
    change (δ - 1 ≤ 0 ∧ 0 ≤ δ) ∧ (-1 ≤ (0 : ℝ) ∧ 0 ≤ 1)
    exact ⟨⟨by linarith, hδ.le⟩, by norm_num⟩
  let P (z : ℂ) : ℂ := ((δ : ℂ) - z) * (2 - ((δ : ℂ) - z))
  have hP (z : ℂ) : (P z).re = 2 * (δ - z.re) - (δ - z.re) ^ 2 + z.im ^ 2 := by
    simp only [P, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
    ring
  have hPnonneg {z : ℂ} (hz : z ∈ U) : 0 ≤ (P z).re := by
    rw [hP]
    obtain ⟨⟨hl, hr⟩, hb, ht⟩ := hz
    have h : 0 ≤ (δ - z.re) * (2 - (δ - z.re)) :=
      mul_nonneg (sub_nonneg.mpr hr) (by linarith)
    nlinarith [sq_nonneg z.im]
  have hPbad {z : ℂ} (hz : z ∈ frontier U) (hr : z.re ≠ δ) : 1 ≤ (P z).re := by
    have hzU := hUclosed.closure_eq ▸ frontier_subset_closure hz
    obtain ⟨⟨hl, hr'⟩, hb, ht⟩ := hzU
    rcases eq_or_lt_of_le hl with hleft | hleft
    · rw [hP, ← hleft]
      ring_nf
      nlinarith [sq_nonneg z.im]
    rcases eq_or_lt_of_le hb with hbottom | hbottom
    · rw [hP, ← hbottom]
      have hh : 0 ≤ (δ - z.re) * (2 - (δ - z.re)) :=
        mul_nonneg (sub_nonneg.mpr hr') (by linarith)
      nlinarith
    rcases eq_or_lt_of_le ht with htop | htop
    · rw [hP, htop]
      have hh : 0 ≤ (δ - z.re) * (2 - (δ - z.re)) :=
        mul_nonneg (sub_nonneg.mpr hr') (by linarith)
      nlinarith
    let V : Set ℂ := {z | (δ - 1 < z.re ∧ z.re < δ) ∧ (-1 < z.im ∧ z.im < 1)}
    have hVopen : IsOpen V :=
      ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const))
    have hVU : V ⊆ U := fun _ h => ⟨⟨h.1.1.le, h.1.2.le⟩, h.2.1.le, h.2.2.le⟩
    exact (hz.2 (interior_maximal hVU hVopen ⟨⟨hleft, lt_of_le_of_ne hr' hr⟩, hbottom, htop⟩)).elim
  refine ⟨max C A, hC.trans (le_max_left _ _), fun i => ?_⟩
  let H (z : ℂ) : ℂ := F z i * Complex.exp (-(M * S i : ℝ) * P z)
  have hH : Differentiable ℂ H := by
    have hΔ : Differentiable ℂ (fun z : ℂ => (δ : ℂ) - z) :=
      (differentiable_const (c := (δ : ℂ))).sub differentiable_id
    have hPt : Differentiable ℂ P :=
      hΔ.mul ((differentiable_const (c := (2 : ℂ))).sub hΔ)
    exact (hF i).mul (Complex.differentiable_exp.comp (hPt.const_mul _))
  have hN (z : ℂ) : ‖H z‖ = ‖F z i‖ * Real.exp (-(M * S i) * (P z).re) := by
    simp [H, Complex.norm_exp, Complex.mul_re]
  have hScale : -(M * S i) ≤ 0 := neg_nonpos.mpr (mul_nonneg hM (hS i))
  have hb : ∀ z ∈ frontier U, ‖H z‖ ≤ max C A * Real.exp (D * δ * S i) := by
    intro z hz
    have hzU : z ∈ U := hUclosed.closure_eq ▸ frontier_subset_closure hz
    rw [hN]
    by_cases hr : z.re = δ
    · have hExp : Real.exp (-(M * S i) * (P z).re) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hScale (hPnonneg hzU))
      exact (mul_le_of_le_one_right (norm_nonneg _) hExp).trans
        ((hAbound z hr (abs_le.mpr hzU.2) i).trans (by gcongr; exact le_max_right _ _))
    · have hExp : -(M * S i) * (P z).re ≤ -(M * S i) := by
        have h := mul_le_mul_of_nonpos_left (hPbad hz hr) hScale
        simpa using h
      calc
        _ ≤ (C * Real.exp (M * S i)) * Real.exp (-(M * S i) * (P z).re) :=
          mul_le_mul_of_nonneg_right (hDisk z (hUdisk hzU) i) (Real.exp_pos _).le
        _ ≤ (C * Real.exp (M * S i)) * Real.exp (-(M * S i)) := by gcongr
        _ = C := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
        _ ≤ max C A * Real.exp (D * δ * S i) :=
          (le_max_left _ _).trans (le_mul_of_one_le_right (hC.trans (le_max_left _ _))
            (Real.one_le_exp (mul_nonneg (mul_nonneg hD hδ.le) (hS i))))
  have h := Complex.norm_le_of_forall_mem_frontier_norm_le hUbounded hH.diffContOnCl hb
    (subset_closure h₀U)
  rw [hN, hP] at h
  simp only [Complex.zero_re, Complex.zero_im, sub_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at h
  have hh := (le_div_iff₀ (Real.exp_pos (-(M * S i) * (2 * δ - δ ^ 2)))).2 h
  rw [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add] at hh
  apply hh.trans
  gcongr
  calc
    D * δ * S i + -(-(M * S i) * (2 * δ - δ ^ 2)) ≤ (D + 2 * M) * δ * S i := by
      have hh' := mul_nonneg (mul_nonneg hM (hS i)) (sq_nonneg δ)
      linarith only [show D * δ * S i + -(-(M * S i) * (2 * δ - δ ^ 2)) + M * S i * δ ^ 2 =
        (D + 2 * M) * δ * S i by ring, hh']
    _ ≤ ε * S i := mul_le_mul_of_nonneg_right hδε (hS i)

end Langlands.Analysis.SeveralComplex
