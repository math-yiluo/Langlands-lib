import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.MeanValue

/-! # Derivative estimates near a slice with vanishing jets -/

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped ContDiff

namespace Langlands.Analysis

universe uX uY uV

variable {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Repeated mean-value bounds from a point whose lower-order jet is zero. -/
theorem norm_iteratedFDeriv_le_of_flat_at_center {f : X → V}
    (hf : ContDiff ℝ ∞ f) (p : X) {N : ℕ}
    (hflat : ∀ j < N, iteratedFDeriv ℝ j f p = 0)
    {C R : ℝ} (hR : 0 ≤ R)
    (hbound : ∀ x ∈ closedBall p R, ‖iteratedFDeriv ℝ N f x‖ ≤ C)
    {j : ℕ} (hj : j ≤ N) {x : X} (hx : x ∈ closedBall p R) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ C * R ^ (N - j) := by
  refine (Nat.decreasingInduction
    (motive := fun j _ => ∀ x ∈ closedBall p R,
      ‖iteratedFDeriv ℝ j f x‖ ≤ C * R ^ (N - j)) ?_ ?_ hj) x hx
  · intro j hj ih x hx
    have hd : Differentiable ℝ (iteratedFDeriv ℝ j f) :=
      (hf.iteratedFDeriv_right (m := (1 : ℕ∞ω)) (by simp)).differentiable (by simp)
    have hc : 0 ≤ C := (norm_nonneg _).trans (hbound p (mem_closedBall_self hR))
    have hm := (convex_closedBall p R).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => hd y)
      (fun y hy => by rw [norm_fderiv_iteratedFDeriv]; exact ih y hy)
      (mem_closedBall_self hR) hx
    rw [hflat j hj, sub_zero] at hm
    have hx' : ‖x - p‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm] using hx
    calc
      _ ≤ (C * R ^ (N - (j + 1))) * ‖x - p‖ := hm
      _ ≤ (C * R ^ (N - (j + 1))) * R :=
        mul_le_mul_of_nonneg_left hx' (mul_nonneg hc (pow_nonneg hR _))
      _ = _ := by rw [mul_assoc, ← pow_succ, show N - (j + 1) + 1 = N - j by omega]
  · intro x hx
    simpa only [Nat.sub_self, pow_zero, mul_one] using hbound x hx

/-- A normal cutoff of width `ε` times a test function flat to order `m`
on the slice has every derivative of order at most `m` uniformly `O(ε)`. -/
theorem exists_norm_iteratedFDeriv_normalCutoff_le {f : X × Y → V} {b : Y → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b)
    (hbs : tsupport b ⊆ closedBall (0 : Y) 1) (m : ℕ)
    (hflat : ∀ x : X, ∀ j ≤ m, iteratedFDeriv ℝ j f (x, (0 : Y)) = 0) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ j ≤ m, ∀ p : X × Y,
        ‖iteratedFDeriv ℝ j (fun q => b (ε⁻¹ • q.2) • f q) p‖ ≤ C j * ε := by
  obtain ⟨C, hC, hCbound⟩ := hfc.exists_bound_iteratedFDeriv hf (m + 1)
  obtain ⟨B, hB, hBbound⟩ := hbc.exists_bound_iteratedFDeriv hb m
  let A (j : ℕ) : ℝ := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B * C
  have hA (j : ℕ) : 0 ≤ A j :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hB) hC
  refine ⟨A, hA, fun ε hε hε₁ j hj p => ?_⟩
  let L : X × Y →L[ℝ] Y := ε⁻¹ • ContinuousLinearMap.snd ℝ X Y
  let ψ : X × Y → ℝ := b ∘ L
  change ‖iteratedFDeriv ℝ j (fun q => ψ q • f q) p‖ ≤ A j * ε
  have hψ : ContDiff ℝ ∞ ψ := hb.comp_continuousLinearMap
  have hL : ‖L‖ ≤ ε⁻¹ :=
    ContinuousLinearMap.opNorm_le_bound L (inv_nonneg.mpr hε.le) (fun q => by
      change ‖ε⁻¹ • q.2‖ ≤ _
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε)]
      exact mul_le_mul_of_nonneg_left (norm_snd_le q) (inv_nonneg.mpr hε.le))
  by_cases hpy : ‖p.2‖ ≤ ε
  · have hψbound (i : ℕ) (hi : i ≤ m) : ‖iteratedFDeriv ℝ i ψ p‖ ≤ B * ε⁻¹ ^ i := by
      change ‖iteratedFDeriv ℝ i (b ∘ L) p‖ ≤ _
      rw [L.iteratedFDeriv_comp_right hb p (by simp)]
      have h := (iteratedFDeriv ℝ i b (L p)).norm_compContinuousLinearMap_le (fun _ => L)
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
      exact h.trans (mul_le_mul (hBbound i hi (L p)) (pow_le_pow_left₀ (norm_nonneg _) hL _)
        (pow_nonneg (norm_nonneg _) _) hB)
    have hfnorm (i : ℕ) (hi : i ≤ m + 1) :
        ‖iteratedFDeriv ℝ i f p‖ ≤ C * ε ^ (m + 1 - i) := by
      have hp : p ∈ closedBall (p.1, (0 : Y)) ε := by
        rcases p with ⟨x, y⟩
        simpa only [mem_closedBall, dist_eq_norm, Prod.mk_sub_mk, sub_self, sub_zero,
          Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] using hpy
      exact norm_iteratedFDeriv_le_of_flat_at_center hf (p.1, 0)
        (fun k hk => hflat p.1 k (by omega)) hε.le
        (fun q _ => hCbound (m + 1) le_rfl q) hi hp
    refine (norm_iteratedFDeriv_smul_le hψ hf p (by simp)).trans ?_
    calc
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B * C * ε := by
        apply Finset.sum_le_sum
        intro i hi
        have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hj₀ : 1 ≤ m + 1 - j := by omega
        have hεpow : ε ^ (m + 1 - j) ≤ ε := by
          simpa only [pow_one] using pow_le_pow_of_le_one hε.le hε₁ hj₀
        calc
          _ ≤ (j.choose i : ℝ) * (B * ε⁻¹ ^ i) * (C * ε ^ (m + 1 - (j - i))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hψbound i (hij.trans hj))
              (Nat.cast_nonneg _)) (hfnorm (j - i) (by omega)) (norm_nonneg _)
              (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hB (pow_nonneg (inv_nonneg.mpr hε.le) _)))
          _ = (j.choose i : ℝ) * B * C * ε ^ (m + 1 - j) := by
            rw [show m + 1 - (j - i) = (m + 1 - j) + i by omega, pow_add, inv_pow]
            field_simp [ne_of_gt hε]
          _ ≤ _ := mul_le_mul_of_nonneg_left hεpow
            (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hB) hC)
      _ = A j * ε := (Finset.sum_mul ..).symm
  · have hs : tsupport (fun q => ψ q • f q) ⊆ {q : X × Y | ‖q.2‖ ≤ ε} := by
      apply closure_minimal _ (isClosed_le continuous_snd.norm continuous_const)
      intro q hq
      have hmem : ε⁻¹ • q.2 ∈ tsupport b := subset_closure (show b (ε⁻¹ • q.2) ≠ 0 from by
        intro hz
        apply hq
        change b (ε⁻¹ • q.2) • f q = 0
        rw [hz, zero_smul])
      have hnorm : ‖ε⁻¹ • q.2‖ ≤ 1 := by
        simpa only [mem_closedBall, dist_zero_right] using hbs hmem
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε)] at hnorm
      exact (inv_mul_le_one₀ hε).mp hnorm
    have hz : iteratedFDeriv ℝ j (fun q => ψ q • f q) p = 0 := by
      by_contra hp
      exact hpy (hs (support_iteratedFDeriv_subset j hp))
    rw [hz, norm_zero]
    exact mul_nonneg (hA j) hε.le

end Langlands.Analysis
