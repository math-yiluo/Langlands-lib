import Langlands.Geometry.Manifold.SmoothGroupChartDerivative
import Mathlib.Analysis.Calculus.MeanValue

/-! # Small oscillation from invariant derivatives near the identity -/

noncomputable section

universe u v

open Set Metric
open scoped Manifold ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Manifold

/-- Finitely many invariant derivative bounds on a fixed compact set near the identity
control the oscillation on an open identity neighborhood. -/
def SmoothGroupLocalOscillationStatement : Prop :=
  ∀ (W : Type u) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (G : Type v) [Group G] [TopologicalSpace G] [ChartedSpace W G] [LieGroup 𝓘(ℝ, W) ∞ G],
    ∃ (K : Set G) (n : ℕ) (X : Fin n → GroupLieAlgebra 𝓘(ℝ, W) G),
      IsCompact K ∧ ∀ (C ε : ℝ), 0 ≤ C → 0 < ε →
      ∃ U : Set G, IsOpen U ∧ 1 ∈ U ∧
        ∀ (f : G → ℂ), ContMDiff 𝓘(ℝ, W) 𝓘(ℝ, ℂ) ∞ f →
          ∀ (s : ℝ), 0 ≤ s →
          (∀ k ∈ K, ∀ j, ‖groupDirectionalValue 𝓘(ℝ, W) (X j) f k‖ ≤ C * s) →
          ∀ y ∈ U, ‖f y - f 1‖ ≤ ε * s

/-- Bound first derivatives in the chart using a fixed finite set of invariant directions and
apply the mean-value estimate on a line segment in a ball inside the chart. -/
theorem smoothGroupLocalOscillation : SmoothGroupLocalOscillationStatement.{u, v} := by
  classical
  intro W _ _ _ G _ _ _ _
  let I := 𝓘(ℝ, W)
  let e := extChartAt I (1 : G)
  let o := e 1
  let ψ : W → G := e.symm
  have he : (1 : G) ∈ e.source := mem_extChartAt_source _
  have ho : o ∈ e.target := e.map_source he
  have hT : IsOpen e.target := isOpen_extChartAt_target (I := I) (1 : G)
  have hψ : ContMDiffOn I I ∞ ψ e.target := contMDiffOn_extChartAt_symm (1 : G)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds ho)
  let B := closedBall o (r / 2)
  have hBT : B ⊆ e.target := (closedBall_subset_ball (half_lt_self hr)).trans hsub
  have hB : IsCompact B := isCompact_closedBall _ _
  let K := ψ '' B
  have hK : IsCompact K := hB.image_of_continuousOn (hψ.continuousOn.mono hBT)
  obtain ⟨X, L, hL, hDeriv⟩ := exists_invariantDerivativeExpansion ψ hT hψ
  have hcoeff (j : Fin (Module.finrank ℝ W)) : ∃ D : ℝ, 0 ≤ D ∧ ∀ y ∈ B, ‖L j y‖ ≤ D := by
    obtain ⟨d, hd⟩ := (hB.image_of_continuousOn ((hL j).continuousOn.norm.mono hBT)).bddAbove
    exact ⟨max 0 d, le_max_left _ _, fun y hy => (hd ⟨y, hy, rfl⟩).trans (le_max_right _ _)⟩
  choose D hD hDbound using hcoeff
  let M := ∑ j, D j
  have hM : 0 ≤ M := Finset.sum_nonneg fun j _ => hD j
  refine ⟨K, Module.finrank ℝ W, X, hK, fun C ε hC hε => ?_⟩
  let δ := min (r / 2) (ε / (1 + M * C))
  have hMC : 0 ≤ M * C := mul_nonneg hM hC
  have hδ : 0 < δ := lt_min (half_pos hr) (div_pos hε (by positivity))
  let U := e.source ∩ e ⁻¹' ball o δ
  have hU : IsOpen U := isOpen_extChartAt_preimage' (I := I) (1 : G) isOpen_ball
  have h1 : (1 : G) ∈ U := ⟨he, mem_ball_self hδ⟩
  refine ⟨U, hU, h1, fun f hf s hs hbound y hy => ?_⟩
  let g := f ∘ ψ
  have hd (z : W) (hz : z ∈ B) : DifferentiableAt ℝ g z :=
    (hDeriv f hf z (hBT hz)).differentiableAt
  have hnorm (z : W) (hz : z ∈ B) : ‖fderiv ℝ g z‖ ≤ M * (C * s) := by
    rw [(hDeriv f hf z (hBT hz)).fderiv]
    calc
      _ ≤ ∑ j, ‖(L j z).smulRight (groupDirectionalValue I (X j) f (ψ z))‖ := norm_sum_le _ _
      _ ≤ ∑ j, D j * (C * s) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [ContinuousLinearMap.norm_smulRight_apply]
        exact mul_le_mul (hDbound j z hz) (hbound (ψ z) ⟨z, hz, rfl⟩ j)
          (norm_nonneg _) (hD j)
      _ = _ := (Finset.sum_mul ..).symm
  have hzB : e y ∈ B := (ball_subset_closedBall.trans
    (closedBall_subset_closedBall (min_le_left _ _))) hy.2
  have hoB : o ∈ B := mem_closedBall_self (half_pos hr).le
  have hmean := (convex_closedBall o (r / 2)).norm_image_sub_le_of_norm_fderiv_le hd hnorm hoB hzB
  change ‖f (e.symm (e y)) - f (e.symm (e 1))‖ ≤ M * (C * s) * ‖e y - o‖ at hmean
  rw [e.left_inv hy.1, e.left_inv he] at hmean
  have hdist : ‖e y - o‖ ≤ ε / (1 + M * C) :=
    (by simpa only [mem_ball, dist_eq_norm] using (show e y ∈ ball o δ from hy.2) :
      ‖e y - o‖ < δ).le.trans (min_le_right _ _)
  have hsmall : M * C * ‖e y - o‖ ≤ ε := by
    calc
      _ ≤ (1 + M * C) * ‖e y - o‖ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (norm_nonneg _)
      _ ≤ ε := by
        rw [mul_comm]
        exact (le_div_iff₀ (by positivity)).mp hdist
  refine hmean.trans ?_
  calc
    _ = (M * C * ‖e y - o‖) * s := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall hs

end Langlands.Geometry.Manifold
