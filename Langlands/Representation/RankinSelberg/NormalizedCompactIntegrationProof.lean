import Langlands.Representation.RankinSelberg.NormalizedCompactIntegrationStatement
import Langlands.Representation.RankinSelberg.CompactIntegrationProof
import Langlands.Representation.Conductor.SphericalIntegrals
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! Compact averages for the actual mass-one integral-subgroup Haar measure. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker

universe uF uV uW

/-- The normalized integral-subgroup Haar average is a uniform finite sum. -/
theorem equalRankNormalizedCompactIntegration {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    EqualRankNormalizedCompactIntegrationStatement.{uF, uV, uW} F T n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
  have hKzero : (Conductor.levelOpenSubgroup F.Carrier n 0 :
      Set (Langlands.GeneralLinear (n + 1) F.Carrier)) = (K : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) := by
    change (Conductor.levelSubgroup F.Carrier n 0 : Set _) = (K : Set (Langlands.GeneralLinear (n + 1) F.Carrier))
    rw [Conductor.levelSubgroup_zero]
  have hKcompact : IsCompact (K : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) := by
    rw [← hKzero]
    exact Conductor.isCompact_levelOpenSubgroup F.Carrier n 0
  have hKmeas : MeasurableSet (K : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) := by
    rw [← hKzero]
    exact (Conductor.levelOpenSubgroup F.Carrier n 0).isOpen.measurableSet
  let κ : Measure K := (generalLinearHaar F.Carrier n).comap Subtype.val
  have hκ : κ Set.univ = 1 := by
    change (generalLinearHaar F.Carrier n).comap
      (Subtype.val : {k : Langlands.GeneralLinear (n + 1) F.Carrier // k ∈ K} → _)
        Set.univ = 1
    calc
      _ = (generalLinearHaar F.Carrier n)
          (Subtype.val '' (Set.univ : Set {k : Langlands.GeneralLinear (n + 1) F.Carrier // k ∈ K})) :=
        comap_subtype_coe_apply hKmeas _ _
      _ = 1 := by
        simp only [Set.image_univ, Subtype.range_val_subtype]
        change (generalLinearHaar F.Carrier n)
          (K : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) = 1
        exact generalLinearHaar_integralSubgroup F.Carrier n
  let : IsFiniteMeasure κ := ⟨by rw [hκ]; exact ENNReal.one_lt_top⟩
  have hdet (k : K) : normalizedAbsoluteValue T (Matrix.det k.val.val) = 1 := by
    have hv := Conductor.valuation_det_of_mem_integralSubgroup k.property
    have hx : Matrix.det k.val.val ≠ 0 := by
      intro hx
      rw [hx, map_zero] at hv
      exact zero_ne_one hv
    have hd : T.discreteValuation (Matrix.det k.val.val) = 1 := by
      change (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier)
        (ValuativeRel.valuation F.Carrier (Matrix.det k.val.val)) = 1
      rw [hv, map_one]
    rw [normalizedAbsoluteValue_apply, T.normalizedAbs_of_ne_zero hx]
    simp [PadicField.TopologicalData.ord, hd]
  intro V _ _ W _ _ π σ hπ hσ ψ ℓ ℓ' f f' Φ
  obtain ⟨m, k, c, hc, hmass, havg⟩ :=
    equalRankCompactIntegration F.Carrier n (K : Set (Langlands.GeneralLinear (n + 1) F.Carrier)) hKcompact κ
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

end Langlands.RankinSelberg
