import Langlands.Representation.RankinSelberg.UnequalRankZeroRowNormalizedCompactIntegrationProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankZeroRowNormalizedCompactIntegrationStatement
/-! Uniform compact averages for the actual zero-row unequal-rank integrand. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnequalRankZeroRowNormalizedCompactIntegrationStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply unequalRankZeroRowNormalizedCompactIntegration
open Langlands.AllField.RankinSelberg

open MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.Whittaker

universe uF uV uW

namespace UnequalRankCompactIntegration
open Langlands.RankinSelberg.UnequalRankCompactIntegration
open Langlands.AllField.RankinSelberg.UnequalRankCompactIntegration
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnequalRankZeroRowNormalizedCompactIntegrationStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply unequalRankZeroRowNormalizedCompactIntegration
open Langlands.AllField.RankinSelberg

private theorem continuous_appendIdentity {F : Type*} [Field F]
    [TopologicalSpace F] (n d : ℕ) :
    Continuous (appendIdentity (F := F) n d) := by
  induction d with
  | zero => exact continuous_id
  | succ d ih =>
      exact (GeneralLinear.rankInclusionContinuous 1).continuous.comp ih

end UnequalRankCompactIntegration

/-- One finite probability-weighted family computes every compact average of
zero-row unequal-rank coefficients, uniformly in the matrix and spectral parameter. -/
theorem unequalRankZeroRowNormalizedCompactIntegration 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n k : ℕ) :
    UnequalRankZeroRowNormalizedCompactIntegrationStatement.{uF, uV, uW} F T n k := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F).integer n
  have hKzero : (Conductor.levelOpenSubgroup F n 0 :
      Set (Langlands.GeneralLinear (n + 1) F)) =
      (K : Set (Langlands.GeneralLinear (n + 1) F)) := by
    change (Conductor.levelSubgroup F n 0 :
      Set (Langlands.GeneralLinear (n + 1) F)) =
      (K : Set (Langlands.GeneralLinear (n + 1) F))
    rw [Conductor.levelSubgroup_zero]
  have hKcompact : IsCompact (K : Set (Langlands.GeneralLinear (n + 1) F)) := by
    rw [← hKzero]
    exact Conductor.isCompact_levelOpenSubgroup F n 0
  have hKmeas : MeasurableSet (K : Set (Langlands.GeneralLinear (n + 1) F)) := by
    rw [← hKzero]
    exact (Conductor.levelOpenSubgroup F n 0).isOpen.measurableSet
  let κ : Measure K := (generalLinearHaar F n).comap Subtype.val
  have hκ : κ Set.univ = 1 := by
    change (generalLinearHaar F n).comap
      (Subtype.val : {u : Langlands.GeneralLinear (n + 1) F // u ∈ K} → _)
        Set.univ = 1
    calc
      _ = (generalLinearHaar F n)
          (Subtype.val '' (Set.univ : Set
            {u : Langlands.GeneralLinear (n + 1) F // u ∈ K})) :=
        comap_subtype_coe_apply hKmeas _ _
      _ = 1 := by
        simp only [Set.image_univ, Subtype.range_val_subtype]
        exact generalLinearHaar_integralSubgroup F n
  let : IsFiniteMeasure κ := ⟨by rw [hκ]; exact ENNReal.one_lt_top⟩
  let : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  have hdet (u : K) : normalizedAbsoluteValue T (Matrix.det u.val.val) = 1 := by
    have hv := Conductor.valuation_det_of_mem_integralSubgroup u.property
    have hx : Matrix.det u.val.val ≠ 0 := by
      intro hx
      rw [hx, map_zero] at hv
      exact zero_ne_one hv
    have hd : T.discreteValuation (Matrix.det u.val.val) = 1 := by
      change (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F)
        (ValuativeRel.valuation F (Matrix.det u.val.val)) = 1
      rw [hv, map_one]
    rw [normalizedAbsoluteValue_apply, T.normalizedAbs_of_ne_zero hx]
    simp [Langlands.LocalFieldData.ord, hd]
  intro V _ _ W _ _ π σ hπ hσ ψ ℓ ℓ' f f'
  obtain ⟨L, hL⟩ := model_isSmooth π hπ ℓ f
  obtain ⟨L', hL'⟩ := model_isSmooth σ hσ ℓ' f'
  let e := appendIdentity (F := F) n (0 + k + 1)
  have he : Continuous e := Langlands.AllField.RankinSelberg.UnequalRankCompactIntegration.continuous_appendIdentity n _
  let J := L.comap e he ⊓ L'
  let D : K → (Langlands.GeneralLinear (n + 1) F ⧸ J.toSubgroup) :=
    fun u => QuotientGroup.mk u.val
  have hD : IsLocallyConstant D :=
    (IsLocallyConstant.iff_continuous D).mpr
      (QuotientGroup.continuous_mk.comp continuous_subtype_val)
  obtain ⟨m, z, c, hc, hmass, havg⟩ :=
    CompactIntegration.finite_average D hD hD.range_finite κ
  refine ⟨m, z, c, hc, ?_, ?_⟩
  · simpa only [measureReal_def, hκ, ENNReal.toReal_one] using hmass
  · intro g s
    have hconst (x y : K) (hxy : D x = D y) :
        unequalRankFunction ψ (normalizedAbsoluteValue T) 0 k f.val f'.val s 0 (g * x.val) =
        unequalRankFunction ψ (normalizedAbsoluteValue T) 0 k f.val f'.val s 0 (g * y.val) := by
      have hj : x.val⁻¹ * y.val ∈ J := QuotientGroup.eq.mp hxy
      have hjL : e (x.val⁻¹ * y.val) ∈ L := hj.1
      have hjL' : x.val⁻¹ * y.val ∈ L' := hj.2
      have hf := congrArg
        (fun w : (coefficientModel π ℓ).toSubmodule => w.val.val (e (g * x.val)))
        (hL ⟨e (x.val⁻¹ * y.val), hjL⟩)
      have hf' := congrArg
        (fun w : (coefficientModel σ ℓ').toSubmodule => w.val.val (g * x.val))
        (hL' ⟨x.val⁻¹ * y.val, hjL'⟩)
      change f.val.val (e (g * x.val) * e (x.val⁻¹ * y.val)) =
        f.val.val (e (g * x.val)) at hf
      change f'.val.val (g * x.val * (x.val⁻¹ * y.val)) =
        f'.val.val (g * x.val) at hf'
      have hfxy : f.val.val (e (g * x.val)) = f.val.val (e (g * y.val)) := by
        simpa only [← map_mul, mul_assoc, mul_inv_cancel_left] using hf.symm
      have hfxy' : f'.val.val (g * x.val) = f'.val.val (g * y.val) := by
        simpa only [mul_assoc, mul_inv_cancel_left] using hf'.symm
      have hweight (u : K) :
          determinantWeight (normalizedAbsoluteValue T) (g * u.val)
              (s - ((0 + k + 1 : ℕ) : ℂ) / 2) =
            determinantWeight (normalizedAbsoluteValue T) g
              (s - ((0 + k + 1 : ℕ) : ℂ) / 2) := by
        simp [determinantWeight, Matrix.det_mul, map_mul, hdet u]
      dsimp only [e] at hfxy
      simp only [unequalRankFunction, unequalRankMatrix_zero_rows, hfxy, hfxy', hweight]
    obtain ⟨hi, hsum, habs⟩ := havg
      (fun u => unequalRankFunction ψ (normalizedAbsoluteValue T) 0 k f.val f'.val s 0
        (g * u.val)) hconst
    refine ⟨(integrableOn_iff_comap_subtypeVal hKmeas).mpr hi, ?_, ?_⟩
    · rw [← integral_subtype_comap hKmeas]
      exact hsum
    · rw [← lintegral_subtype_comap hKmeas]
      exact habs

end Langlands.AllField.RankinSelberg
