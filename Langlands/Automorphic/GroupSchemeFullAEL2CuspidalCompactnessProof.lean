import Langlands.Automorphic.GroupSchemeFullAEL2CuspidalCompactnessStatement
import Langlands.Automorphic.GroupSchemeCuspidalConvolutionCompact
import Langlands.Automorphic.GroupSchemePositiveMatrixEmbedding
import Langlands.Global.AdelicLocalizedConvolutionApproximation
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.Representation.Unitary.IntegratedConvolutionProof

/-! # Compactness by approximation of continuous cuspidal convolutions -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Filter MeasureTheory Set Topology
open scoped CategoryTheory.MonObj CompactlySupported Pointwise

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global AdelicGroupPoints PositiveRealTorus Langlands.GroupScheme
open Langlands.Analysis

set_option maxHeartbeats 4000000 in
/-- All continuous compactly supported weights give compact original cuspidal operators. -/
theorem groupSchemeFullAEL2CuspidalCompactness :
    GroupSchemeFullAEL2CuspidalCompactnessStatement.{u} := by
  intro F _ _ G _ _ hPD hG T i hi _ I _ e hc _
  dsimp only
  intro f hf
  let A := AdelicGroupPoints F G
  let S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
  let μG : Measure A := Measure.haar
  let R := fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc μG
  let πc := fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc
  let hπnorm := norm_fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc
  let hπmeas := fullAEL2CuspidalOrbit_aestronglyMeasurable F G hPD hG T i hi I e hc μG
  let hsmooth := hG.smoothDimension_spec
  obtain ⟨_, σ, hσ⟩ := affineLinearEmbeddingStatement F G hG.isAffineHom inferInstance
  obtain ⟨_, ρ, hn, hρ, _⟩ := exists_positiveMatrixEmbedding_of_isClosedSubgroup
    σ hσ hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)
  have htestCompact (h : C_c(A, ℂ)) (hh : Integrable h μG) (hhTest : IsAdelicTestFunction F G h) :
      IsCompactOperator (R h hh) :=
    (groupSchemeCuspidalConvolutionCompact T i hi I e hc hG ρ hPD hn hρ h hh hhTest).2
  change IsCompactOperator (R f hf)
  apply isClosed_setOfPred_isCompactOperator.closure_subset
  refine Metric.mem_closure_iff.2 fun ε hε => ?_
  obtain ⟨V, hVc, hV⟩ := exists_compact_mem_nhds (1 : A)
  let D : Set A := V * tsupport f ∪ tsupport f
  have hDc : IsCompact D := (hVc.mul f.hasCompactSupport).union f.hasCompactSupport
  have hD : MeasurableSet D := hDc.isClosed.measurableSet
  let M : ℝ := μG.real D
  have hM : 0 ≤ M := measureReal_nonneg
  let δ := ε / (M + 1)
  have hM1 : 0 < M + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hM1
  let fInv : C(A, ℂ) := ⟨fun x => f x⁻¹, f.continuous.comp continuous_inv⟩
  obtain ⟨h, hh, hs, hApprox⟩ := exists_rightConvolution_approximation_in_nhds
    hG.smoothDimension_spec (fun _ : Fin 1 => fInv) hV hDc.inv hδ
  let h₀ : C_c(A, ℂ) := ⟨⟨h, hh.1.1⟩, hh.2.1⟩
  have hhInt : Integrable h μG := h₀.continuous.integrable_of_hasCompactSupport h₀.hasCompactSupport
  let c := Hecke.convolutionIntegral μG h f
  obtain ⟨hcInt, hcomp⟩ := integratedActionConvolution A S μG πc hπnorm hπmeas h f hhInt hf
  change R c hcInt = (R h hhInt).comp (R f hf) at hcomp
  have hcCompact : IsCompactOperator (R c hcInt) := by
    rw [hcomp]
    exact (htestCompact h₀ hhInt hh).comp_clm _
  have hEq (x : A) : c x = rightConvolution F G h fInv x⁻¹ := by
    simp only [c, rightConvolution, Hecke.convolutionIntegral, fInv, ContinuousMap.coe_mk,
      mul_inv_rev, inv_inv, μG]
    rfl
  have hle (x : A) : ‖c x - f x‖ ≤ D.indicator (fun _ => δ) x := by
    by_cases hx : x ∈ D
    · rw [indicator_of_mem hx, hEq]
      have hinv : x⁻¹ ∈ D⁻¹ := by
        change x⁻¹⁻¹ ∈ D
        rwa [inv_inv]
      simpa only [fInv, ContinuousMap.coe_mk, inv_inv] using hApprox 0 x⁻¹ hinv
    · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport
        (fun hxf => hx (Or.inr hxf))]
      suffices c x = 0 by simp [this]
      apply integral_eq_zero_of_ae
      exact Eventually.of_forall fun a => by
        by_contra hne
        obtain ⟨ha, hf'⟩ := mul_ne_zero_iff.mp hne
        exact hx (Or.inl ⟨a, hs a ha, a⁻¹ * x, subset_tsupport _ hf', by simp⟩)
  have hIntDiff : Integrable (fun x => c x - f x) μG := hcInt.sub hf
  have hdiff : R c hcInt - R f hf = R (fun x => c x - f x) hIntDiff := by
    apply ContinuousLinearMap.ext
    intro φ
    change (∫ a, c a • πc a φ ∂μG) - (∫ a, f a • πc a φ ∂μG) =
      ∫ a, (c a - f a) • πc a φ ∂μG
    rw [← integral_sub
      (isometricActionIntegrand_integrable μG πc hπnorm hπmeas c hcInt φ)
      (isometricActionIntegrand_integrable μG πc hπnorm hπmeas f hf φ)]
    apply integral_congr_ae
    exact Eventually.of_forall fun a => (sub_smul (c a) (f a) (πc a φ)).symm
  have hInd : Integrable (D.indicator (fun _ => δ)) μG :=
    (integrable_indicator_iff hD).2 (integrableOn_const (C := δ) (hs := hDc.measure_lt_top.ne))
  have hIntegral : (∫ x, ‖c x - f x‖ ∂μG) ≤ M * δ := by
    simpa only [integral_indicator_const δ hD, smul_eq_mul, M] using
      integral_mono_ae hIntDiff.norm hInd (Eventually.of_forall hle)
  have hdist : ‖R c hcInt - R f hf‖ < ε := by
    rw [hdiff]
    calc
      _ ≤ ∫ x, ‖c x - f x‖ ∂μG :=
        norm_fullAEL2CuspidalIntegratedAction_le F G hPD hG T i hi I e hc μG _ hIntDiff
      _ ≤ M * δ := hIntegral
      _ < (M + 1) * δ := mul_lt_mul_of_pos_right (lt_add_one M) hδ
      _ = ε := by rw [mul_comm, div_mul_cancel₀ _ hM1.ne']
  exact ⟨R c hcInt, hcCompact, by rw [dist_comm, dist_eq_norm]; exact hdist⟩

end Langlands.Automorphic.GroupSchemeFunctions
