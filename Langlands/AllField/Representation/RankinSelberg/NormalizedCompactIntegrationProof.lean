import Langlands.Representation.RankinSelberg.NormalizedCompactIntegrationProof
import Langlands.AllField.Representation.RankinSelberg.NormalizedCompactIntegrationStatement
/-! Compact averages for the actual mass-one integral-subgroup Haar measure. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankNormalizedCompactIntegrationStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement equalRankNormalizedCompactIntegration normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.Whittaker

universe uF uV uW

/-- The normalized integral-subgroup Haar average is a uniform finite sum. -/
theorem equalRankNormalizedCompactIntegration 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) :
    EqualRankNormalizedCompactIntegrationStatement.{uF, uV, uW} F T n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F).integer n
  have hKzero : (Conductor.levelOpenSubgroup F n 0 :
      Set (Langlands.GeneralLinear (n + 1) F)) = (K : Set (Langlands.GeneralLinear (n + 1) F)) := by
    change (Conductor.levelSubgroup F n 0 : Set _) = (K : Set (Langlands.GeneralLinear (n + 1) F))
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
      (Subtype.val : {k : Langlands.GeneralLinear (n + 1) F // k ∈ K} → _)
        Set.univ = 1
    calc
      _ = (generalLinearHaar F n)
          (Subtype.val '' (Set.univ : Set {k : Langlands.GeneralLinear (n + 1) F // k ∈ K})) :=
        comap_subtype_coe_apply hKmeas _ _
      _ = 1 := by
        simp only [Set.image_univ, Subtype.range_val_subtype]
        change (generalLinearHaar F n)
          (K : Set (Langlands.GeneralLinear (n + 1) F)) = 1
        exact generalLinearHaar_integralSubgroup F n
  let : IsFiniteMeasure κ := ⟨by rw [hκ]; exact ENNReal.one_lt_top⟩
  have hdet (k : K) : normalizedAbsoluteValue T (Matrix.det k.val.val) = 1 := by
    have hv := Conductor.valuation_det_of_mem_integralSubgroup k.property
    have hx : Matrix.det k.val.val ≠ 0 := by
      intro hx
      rw [hx, map_zero] at hv
      exact zero_ne_one hv
    have hd : T.discreteValuation (Matrix.det k.val.val) = 1 := by
      change (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F)
        (ValuativeRel.valuation F (Matrix.det k.val.val)) = 1
      rw [hv, map_one]
    rw [normalizedAbsoluteValue_apply, T.normalizedAbs_of_ne_zero hx]
    simp [Langlands.LocalFieldData.ord, hd]
  intro V _ _ W _ _ π σ hπ hσ ψ ℓ ℓ' f f' Φ
  obtain ⟨m, k, c, hc, hmass, havg⟩ :=
    equalRankCompactIntegration F n (K : Set (Langlands.GeneralLinear (n + 1) F)) hKcompact κ
      (normalizedAbsoluteValue T) hdet V W π σ hπ hσ ψ ℓ ℓ' f f' Φ
  refine ⟨m, k, c, hc, ?_, ?_⟩
  · simpa only [measureReal_def, hκ, ENNReal.toReal_one] using hmass
  · intro g s
    obtain ⟨hi, hsum, habs⟩ := havg g s
    refine ⟨(integrableOn_iff_comap_subtypeVal hKmeas).mpr hi, ?_, ?_⟩
    · rw [← integral_subtype_comap hKmeas]
      exact hsum
    · rw [← lintegral_subtype_comap hKmeas]
      exact habs

end Langlands.AllField.RankinSelberg
