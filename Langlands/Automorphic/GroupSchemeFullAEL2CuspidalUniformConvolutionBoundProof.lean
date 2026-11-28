import Langlands.Automorphic.GroupSchemeCuspidalConvolutionCompact
import Langlands.Automorphic.GroupSchemeFullAEL2CuspidalUniformConvolutionBoundStatement
import Langlands.Automorphic.GroupSchemePositiveMatrixEmbedding
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-! # Uniform evaluation of smoothed cuspidal vectors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported InnerProductSpace

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.InfiniteAdelicGroupPoints Langlands.Global.PositiveRealTorus
open Langlands.GroupScheme RepresentationGrowth

set_option maxHeartbeats 1000000 in
/-- Evaluation of every smooth cuspidal convolution is uniformly bounded by the input norm. -/
theorem groupSchemeFullAEL2CuspidalUniformConvolutionBound :
    GroupSchemeFullAEL2CuspidalUniformConvolutionBoundStatement.{u} := by
  open Langlands.QuotientIntegration in
  intro F _ _ G _ _ hPD hG T i hi _ I _ e hc _
  dsimp only
  intro f hf htest
  let A := AdelicGroupPoints F G
  let H := positiveRationalSubgroup F G T i
  let Q := PositiveRationalQuotient F G T i
  let μG : Measure A := Measure.haar
  let μQ := positiveRationalQuotientHaarMeasure F G T i
  let S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
  let R := fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc μG f hf
  let j := fullAEL2CuspidalInclusionLI F G hPD hG T i hi I e hc
  let mk := LeftCosetSpace.mk H
  let ψ (φ : S) := positiveQuotientLpSmoothing T i f φ.val
  let := positiveRationalQuotient_borelSpace F G T i hi I e hc
  let := positiveRationalQuotientHaarMeasure_isLocallyFiniteMeasure F G T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_isHaarMeasure F G T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_sigmaFinite F G T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_isMulRightInvariant F G T i hi I e hc
  let hsmooth := hG.smoothDimension_spec
  have hRep (φ : S) : ∃ v : C(Q, ℂ), (∀ x, v (mk x) = ψ φ x) ∧
      ((R φ).val : Q → ℂ) =ᵐ[μQ] v := by
    have hmeas : Measurable (fun x => φ.val (mk x)) :=
      (Lp.stronglyMeasurable φ.val).measurable.comp (LeftCosetSpace.continuous_mk H).measurable
    have hloc := locallyIntegrable_positiveQuotientLpPullback T i hi I e hc φ.val
    have hs := (adelicRightConvolutionDifferentiation F G _ hsmooth f _ htest hmeas hloc).2.1
    have hInv := positiveQuotientLpSmoothing_invariant T i f φ.val
    let v : C(Q, ℂ) := ⟨LeftCosetSpace.lift H (ψ φ) hInv,
      LeftCosetSpace.continuous_lift H (ψ φ) hInv hs.1⟩
    refine ⟨v, fun _ => rfl, ?_⟩
    rw [fullAEL2CuspidalIntegratedAction_val]
    exact positiveQuotientLpSmoothing_ae_eq T i hi I e hc f hf φ.val
  obtain ⟨k, _, hk, _⟩ := quotientConvolutionKernel H
    (isClosed_positiveRationalSubgroup F G T i hi I e hc)
    (positiveRationalSubgroupHaarMeasure F G T i hi I e hc) μG μQ
    (positiveRationalQuotientHaarMeasure_isCompatible F G T i hi I e hc) f
  let eval (x : A) : S →L[ℂ] ℂ := (innerSL ℂ (k x)).comp j.toContinuousLinearMap
  have hEval (x : A) (φ : S) : eval x φ = ψ φ x := (hk x φ.val).2
  have hPointwise : ∀ φ : S, ∃ B : ℝ, ∀ x : A, ‖eval x φ‖ ≤ B := by
    obtain ⟨_, σ, hσ⟩ := affineLinearEmbeddingStatement F G hG.isAffineHom inferInstance
    obtain ⟨_, ρ, hn, hρ, _⟩ := exists_positiveMatrixEmbedding_of_isClosedSubgroup
      σ hσ hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)
    obtain ⟨D, _, hD, hDecay⟩ := adelicNormOneCuspidalRapidDecay hsmooth ρ hG hn
    obtain ⟨m, hGrowth⟩ :=
      positiveQuotientLpSmoothing_globalGrowth T i hi I e hc hG hsmooth ρ hn hρ
    obtain ⟨hSmooth, hGrowth⟩ := hGrowth f htest
    intro φ
    obtain ⟨v, hv, hvAE⟩ := hRep φ
    let fv := positiveQuotientContinuousPullback F G T i v
    have hfv : evaluate F G fv = ψ φ := funext hv
    have hCusp : HasZeroProperParabolicConstantTerms (ψ φ) := by
      rw [← hfv]
      apply hasZeroProperParabolicConstantTerms_of_normalized hPD hG
      exact ((groupSchemeFullAEL2ContinuousCuspidality F G hPD hG T i hi I e hc v
        (R φ).val hvAE).mp (R φ).property)
    have hInv : IsLeftInvariantUnder F G (rationalSubgroup F G) (ψ φ) := fun r hr x =>
      positiveQuotientLpSmoothing_invariant T i f φ.val
        ⟨r, rationalSubgroup_le_positiveRationalSubgroup F G T i hr⟩ x
    have hWord (s : List (smoothModel F hG.smoothDimension)) :
        ∃ C : ℝ, 0 ≤ C ∧ ∀ x : A,
          ‖adelicIteratedDirectionalValue hsmooth s (ψ φ) x‖ ≤
            C * adelicHeight F G ρ x ^ (m : ℝ) := by
      obtain ⟨B, hB, hBφ⟩ := hGrowth s
      refine ⟨B * ‖φ‖, mul_nonneg hB (norm_nonneg _), fun x => ?_⟩
      change ‖adelicIteratedDirectionalValue hsmooth s (ψ φ) x‖ ≤
        (B * ‖φ.val‖) * adelicHeight F G ρ x ^ (m : ℝ)
      rw [Real.rpow_natCast, mul_right_comm B]
      exact hBφ φ.val x
    obtain ⟨B, _, hB⟩ := hDecay (ψ φ) (hSmooth φ.val) hInv hCusp m
      (Nat.cast_nonneg _) hWord 0
    refine ⟨B, fun x => ?_⟩
    let n₀ := normOneProjection F G T i hi I e hc x
    obtain ⟨q, hq⟩ := hD n₀
    have hmk : mk n₀.val = mk x := by
      have h := (positiveQuotientHomeomorph F G T i hi I e hc).apply_symm_apply (mk x)
      change positiveQuotientHomeomorph F G T i hi I e hc
        (LeftCosetSpace.mk (rationalNormOneSubgroup F G) n₀) = mk x at h
      simpa only [positiveQuotientHomeomorph_mk] using h
    rw [hEval, ← hv x, ← hmk, hv, ← hInv _ ⟨q, rfl⟩ n₀.val]
    simpa only [pow_zero, mul_one] using hB _ hq
  obtain ⟨C, hC⟩ := banach_steinhaus (g := eval) hPointwise
  refine ⟨max 0 C, le_max_left _ _, fun φ => ?_⟩
  obtain ⟨v, hv, hvAE⟩ := hRep φ
  refine ⟨v, hvAE, fun q => ?_⟩
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective H q
  rw [hv x, ← hEval]
  exact ((eval x).le_opNorm φ).trans
    (mul_le_mul_of_nonneg_right ((hC x).trans (le_max_right _ _)) (norm_nonneg _))

end Langlands.Automorphic.GroupSchemeFunctions
