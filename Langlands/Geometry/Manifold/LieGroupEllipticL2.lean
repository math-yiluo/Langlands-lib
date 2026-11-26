import Langlands.Geometry.Manifold.LieGroupChartHaarBound
import Langlands.Geometry.Manifold.LieGroupEllipticEstimateProof

/-! # Local Haar `L²` control of evaluation for an elliptic word equation -/

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ContDiff ENNReal Manifold Topology

set_option autoImplicit false

namespace Langlands.Geometry.Manifold

open Langlands.Analysis

/-- Evaluation at the identity of a smooth solution to one positive-order elliptic word
operator is bounded by its `L²` norm on a fixed compact subset of the Lie group. -/
theorem exists_lieWord_l2_evaluation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [Group H] [TopologicalSpace H] [ChartedSpace E H]
    [LieGroup 𝓘(ℝ, E) ∞ H] [IsTopologicalGroup H] [SecondCountableTopology H] [T2Space H]
    [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsHaarMeasure]
    {n r : ℕ} (hr : 0 < r) (X : Fin n → GroupLieAlgebra 𝓘(ℝ, E) H)
    (Ptop Plow : MonoidAlgebra ℂ (FreeMonoid (Fin n)))
    (htop : ∀ w ∈ Ptop.coeff.support, w.length = r)
    (hlow : ∀ w ∈ Plow.coeff.support, w.length < r)
    (hell : ∀ ξ : GroupLieAlgebra 𝓘(ℝ, E) H →ₗ[ℝ] ℝ, ξ ≠ 0 → lieWordSymbol X ξ Ptop ≠ 0) :
    ∃ (V : Set H) (C : ℝ≥0∞), IsCompact V ∧ C ≠ ⊤ ∧
      ∀ φ : H → ℂ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ φ →
        (∀ x, lieWordAction X (Ptop + Plow) φ x = 0) →
        ‖φ 1‖ₑ ≤ C * eLpNorm φ 2 (μ.restrict V) := by
  let d := Module.finrank ℝ E
  let F := EuclideanSpace ℝ (Fin d)
  let L : E ≃L[ℝ] F := toEuclidean
  let e := extChartAt 𝓘(ℝ, E) (1 : H)
  let S := L.symm ⁻¹' e.target
  let ψ := e.symm ∘ L.symm
  let x₀ := L (e 1)
  obtain ⟨D, _, _, _, hψ₀, hψ, hD, hcoef, hellD, haction, _⟩ :=
    exists_lieWordCoordinateOperator X Ptop Plow htop hlow hell
  obtain ⟨R, hR, hRS, c, hc, hdom⟩ := exists_chartVolume_le_smul_haar (E := E) μ
  have hballS : ball x₀ R ⊆ S := ball_subset_closedBall.trans hRS
  obtain ⟨ρ, _, hρR, C, hC, hest⟩ := exists_localElliptic_interior_derivative_l2_bounds
    hr D hD isOpen_ball (fun k w => (hcoef k w).mono hballS) (mem_ball_self hR) hellD
  let V := ψ '' closedBall x₀ R
  have hV : IsCompact V := (isCompact_closedBall _ _).image_of_continuousOn (hψ.continuousOn.mono hRS)
  let ν := (volume : Measure F).restrict (closedBall x₀ R)
  have hψm : AEMeasurable ψ ν :=
    (hψ.continuousOn.mono hRS).aemeasurable measurableSet_closedBall
  have hνV : (ν.map ψ).restrict V = ν.map ψ := by
    apply Measure.restrict_eq_self_of_ae_mem
    refine (ae_map_iff hψm hV.measurableSet).mpr ?_
    exact ae_restrict_of_forall_mem measurableSet_closedBall fun x hx => mem_image_of_mem ψ hx
  have hbound : ν.map ψ ≤ c • μ.restrict V := by
    rw [← Measure.restrict_smul, ← hνV]
    exact Measure.restrict_mono_measure hdom V
  refine ⟨V, C 0 * c ^ (1 / 2 : ℝ), hV,
    ENNReal.mul_ne_top (hC 0) (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hc), ?_⟩
  intro φ hφ hsol
  have hφψ := contMDiffOn_iff_contDiffOn.mp (hφ.comp_contMDiffOn hψ)
  have hφD (x : F) (hx : x ∈ ball x₀ R) : D.action (φ ∘ ψ) x = 0 :=
    (haction φ hφ x (hballS hx)).trans (hsol (ψ x))
  have hEval := hest (φ ∘ ψ) (hφψ.mono hballS) hφD 0
  change ψ x₀ = 1 at hψ₀
  have hval : ‖iteratedFDeriv ℝ 0 (φ ∘ ψ) x₀‖ₑ = ‖φ 1‖ₑ := by
    rw [← ENNReal.ofReal_toReal (enorm_ne_top : ‖iteratedFDeriv ℝ 0 (φ ∘ ψ) x₀‖ₑ ≠ ⊤),
      ← ENNReal.ofReal_toReal (enorm_ne_top : ‖φ 1‖ₑ ≠ ⊤), toReal_enorm, toReal_enorm,
      norm_iteratedFDeriv_zero, Function.comp_apply, hψ₀]
  rw [hval] at hEval
  have hLp : eLpNorm (φ ∘ ψ) 2 (volume.restrict (closedBall x₀ ρ)) ≤ eLpNorm φ 2 (ν.map ψ) := by
    rw [eLpNorm_map_measure hφ.continuous.aestronglyMeasurable hψm]
    exact eLpNorm_mono_measure _ (Measure.restrict_mono_set _ (hρR.trans ball_subset_closedBall))
  have hLp' := eLpNorm_le_of_measure_le_smul hbound (f := φ) (p := 2)
  have hhalf : (1 / (2 : ℝ≥0∞)).toReal = (1 / 2 : ℝ) := by norm_num
  rw [hhalf, smul_eq_mul] at hLp'
  rw [mul_assoc]
  exact hEval.trans (mul_le_mul' le_rfl (hLp.trans hLp'))

end Langlands.Geometry.Manifold
