import Langlands.HarmonicAnalysis.Distribution.FlatProductJets

/-! # Weighted estimates for cutoff errors near a coordinate subspace -/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Distributions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.HarmonicAnalysis

universe u v

private theorem norm_iteratedFDeriv_le_sup {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {K : Compacts X} (f : 𝓓_{K}(X, ℝ)) {i m : ℕ} (hi : i ≤ m) (x : X) :
    ‖iteratedFDeriv ℝ i f x‖ ≤ ContDiffMapSupportedIn.supSeminorm ℝ X ℝ ⊤ K m f :=
  (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ).trans
    ((Finset.le_sup (f := ContDiffMapSupportedIn.seminorm ℝ X ℝ ⊤ K)
      (Finset.mem_Iic.mpr hi)) f)

variable {E : Type u} {N : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup N] [NormedSpace ℝ N]
  [FiniteDimensional ℝ N]

/-- After dividing by a prescribed transverse vanishing power, the near-section
cutoff of a sufficiently flat test tends to zero at inverse scale. -/
theorem exists_weighted_normalCutoff_bound (d m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : Compacts (E × N)} (f : 𝓓_{K}(E × N, ℝ)),
      (∀ x : E, ∀ i ≤ d + m, iteratedFDeriv ℝ i f (x, 0) = 0) →
      ∀ (t : ℝ), 1 ≤ t → ∀ j ≤ d, ∀ x : E × N,
        ‖iteratedFDeriv ℝ j (normalCutoffTest t f) x‖ ≤
          (C * ContDiffMapSupportedIn.supSeminorm ℝ (E × N) ℝ ⊤ K (d + m + 1) f) * ‖x.2‖ ^ m * t⁻¹ := by
  let B : Compacts N := ⟨Metric.closedBall 0 1, isCompact_closedBall _ _⟩
  let b : ContDiffBump (0 : N) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let χ : 𝓓_{B}(N, ℝ) := ContDiffMapSupportedIn.of_support_subset b.contDiff (by
    rw [b.support_eq]
    exact Metric.ball_subset_closedBall)
  let C₀ := ContDiffMapSupportedIn.supSeminorm ℝ N ℝ ⊤ B d χ
  let C := ∑ j ∈ Finset.Iic d, ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * C₀
  have hC₀ : 0 ≤ C₀ := apply_nonneg _ _
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro K f hFlat t ht j hj x
  let A := ContDiffMapSupportedIn.supSeminorm ℝ (E × N) ℝ ⊤ K (d + m + 1) f
  have hA : 0 ≤ A := apply_nonneg _ _
  have ht₀ := zero_lt_one.trans_le ht
  let L : E × N →L[ℝ] N := t • ContinuousLinearMap.snd ℝ E N
  have hL : ‖L‖ ≤ t := by
    change ‖t • ContinuousLinearMap.snd ℝ E N‖ ≤ t
    rw [norm_smul, Real.norm_of_nonneg ht₀.le]
    exact mul_le_of_le_one_right ht₀.le (ContinuousLinearMap.norm_snd_le _ _ _)
  have hχ (i : ℕ) (hi : i ≤ d) : ‖iteratedFDeriv ℝ i (χ ∘ L) x‖ ≤ C₀ * t ^ i := by
    rw [L.iteratedFDeriv_comp_right χ.contDiff x (by simp)]
    calc
      _ ≤ ‖iteratedFDeriv ℝ i χ (L x)‖ * ∏ _ : Fin i, ‖L‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ = ‖iteratedFDeriv ℝ i χ (L x)‖ * ‖L‖ ^ i := by simp
      _ ≤ C₀ * t ^ i := by
        gcongr
        exact norm_iteratedFDeriv_le_sup χ hi (L x)
  change ‖iteratedFDeriv ℝ j (fun y => (χ ∘ L) y * f y) x‖ ≤ (C * A) * ‖x.2‖ ^ m * t⁻¹
  refine (norm_iteratedFDeriv_mul_le (χ.contDiff.comp L.contDiff) f.contDiff x (by simp)).trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), ((j.choose i : ℝ) * C₀) * (A * ‖x.2‖ ^ m * t⁻¹) := by
      apply Finset.sum_le_sum
      intro i hi
      have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      by_cases hB : L x ∈ (B : Set N)
      · have hNorm : ‖x.2‖ ≤ t⁻¹ := by
          have h : ‖L x‖ ≤ 1 := by
            simpa only [B, Compacts.coe_mk, Metric.mem_closedBall, dist_zero_right] using hB
          change ‖t • x.2‖ ≤ 1 at h
          rw [norm_smul, Real.norm_of_nonneg ht₀.le] at h
          rw [← one_div, le_div_iff₀ ht₀, mul_comm]
          exact h
        have hDecay : ‖iteratedFDeriv ℝ (j - i) f x‖ ≤ A * (‖x.2‖ ^ m * (t⁻¹) ^ (i + 1)) := by
          have h := norm_iteratedFDeriv_le_pow_of_flat f.contDiff (x.1, 0) (d + m) hA
            (hFlat x.1) (fun l hl y => norm_iteratedFDeriv_le_sup f hl y)
            (m + (i + 1)) (j - i) (by omega) x
          have hx : ‖x - (x.1, 0)‖ = ‖x.2‖ := by simp [Prod.norm_def]
          rw [hx, pow_add] at h
          exact h.trans (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hNorm _) (pow_nonneg (norm_nonneg _) _)) hA)
        calc
          _ ≤ (j.choose i : ℝ) * (C₀ * t ^ i) * (A * (‖x.2‖ ^ m * (t⁻¹) ^ (i + 1))) := by
            gcongr
            exact hχ i (hij.trans hj)
          _ = (j.choose i : ℝ) * C₀ * (A * ‖x.2‖ ^ m * t⁻¹) * (t ^ i * (t⁻¹) ^ i) := by
            rw [pow_succ]
            ring
          _ = _ := by rw [← mul_pow, mul_inv_cancel₀ ht₀.ne', one_pow, mul_one]
      · have hz : iteratedFDeriv ℝ i (χ ∘ L) x = 0 := by
          rw [L.iteratedFDeriv_comp_right χ.contDiff x (by simp)]
          rw [show iteratedFDeriv ℝ i χ (L x) = 0 from χ.iteratedFDeriv_zero_on_compl hB]
          ext v
          rfl
        rw [hz, norm_zero, mul_zero, zero_mul]
        positivity
    _ ≤ _ := by
      rw [← Finset.sum_mul, mul_assoc C A, mul_assoc C (A * ‖x.2‖ ^ m), mul_assoc A]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact Finset.single_le_sum
        (f := fun j : ℕ => ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * C₀)
        (fun j _ => by positivity) (Finset.mem_Iic.mpr hj)

/-- The uniform weighted derivative estimate for the cutoff of a flat test. -/
def WeightedNormalCutoffStatement : Prop :=
  ∀ (E : Type u) (N : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N] (d m : ℕ),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : Compacts (E × N)} (f : 𝓓_{K}(E × N, ℝ)),
      (∀ x : E, ∀ i ≤ d + m, iteratedFDeriv ℝ i f (x, 0) = 0) →
      ∀ (t : ℝ), 1 ≤ t → ∀ j ≤ d, ∀ x : E × N,
        ‖iteratedFDeriv ℝ j (normalCutoffTest t f) x‖ ≤
          (C * ContDiffMapSupportedIn.supSeminorm ℝ (E × N) ℝ ⊤ K (d + m + 1) f) * ‖x.2‖ ^ m * t⁻¹

theorem weightedNormalCutoff : WeightedNormalCutoffStatement.{u, v} := by
  intro E N _ _ _ _ _ d m
  exact exists_weighted_normalCutoff_bound d m

end Langlands.HarmonicAnalysis
