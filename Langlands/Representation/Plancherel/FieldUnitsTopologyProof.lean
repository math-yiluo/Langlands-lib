import Langlands.Representation.Plancherel.FieldUnitsTopologyStatement
import Mathlib.Topology.Algebra.Group.Units

/-! # Continuity of the actual normalized local-field maps -/

open scoped NNReal WithZero Topology
open Filter

namespace Langlands.Plancherel

universe uF

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

private theorem normalizedAbsoluteValue_mono {x y : F}
    (h : ValuativeRel.valuation F x ≤ ValuativeRel.valuation F y) :
    LocalField.residueNormalizedAbsoluteValue F x ≤
      LocalField.residueNormalizedAbsoluteValue F y := by
  have hq : (1 : ℝ≥0) < (LocalField.residueCardinality F : ℝ≥0) := by
    exact_mod_cast LocalField.residueCardinality_gt_one F
  change (WithZeroMulInt.toNNReal hq.ne_zero
      (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
        (ValuativeRel.valuation F x)) : ℝ) ≤
    (WithZeroMulInt.toNNReal hq.ne_zero
      (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
        (ValuativeRel.valuation F y)) : ℝ)
  exact NNReal.coe_le_coe.mpr ((WithZeroMulInt.toNNReal_strictMono hq).monotone
    ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).strictMono.monotone h))

/-- Continuity of the actual normalized absolute value, including at zero. -/
theorem continuous_residueNormalizedAbsoluteValue :
    Continuous (LocalField.residueNormalizedAbsoluteValue F) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    rw [ContinuousAt, map_zero]
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hq : (1 : ℝ) < (LocalField.residueCardinality F : ℝ) := by
      exact_mod_cast LocalField.residueCardinality_gt_one F
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hq)
    have hball : {y : F | ValuativeRel.valuation F y <
        ValuativeRel.valuation F (LocalField.uniformizer F ^ n)} ∈ 𝓝 (0 : F) :=
      (IsValuativeTopology.hasBasis_nhds_zero' F).mem_of_mem
        ((ValuativeRel.valuation F).ne_zero_iff.mpr
          (pow_ne_zero n (LocalField.uniformizer_ne_zero F)))
    filter_upwards [hball] with y hy
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg ((LocalField.residueNormalizedAbsoluteValue F).nonneg y)]
    calc
      LocalField.residueNormalizedAbsoluteValue F y ≤
          LocalField.residueNormalizedAbsoluteValue F (LocalField.uniformizer F ^ n) :=
        normalizedAbsoluteValue_mono F hy.le
      _ = ((LocalField.residueCardinality F : ℝ)⁻¹) ^ n := by
        rw [map_pow, LocalField.residueNormalizedAbsoluteValue_of_ord_one F
          (LocalField.ord_uniformizer F)]
      _ < ε := hn
  · have hval := (ValuativeRel.valuation F).locally_const
      ((ValuativeRel.valuation F).ne_zero_iff.mpr hx)
    apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [hval] with y hy
    exact le_antisymm (normalizedAbsoluteValue_mono F hy.le)
      (normalizedAbsoluteValue_mono F hy.ge)

private theorem units_valuation_isLocallyConstant :
    IsLocallyConstant (fun a : Fˣ => ValuativeRel.valuation F (a : F)) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro a
  exact Units.continuous_val.continuousAt.preimage_mem_nhds
    ((ValuativeRel.valuation F).locally_const
      ((ValuativeRel.valuation F).ne_zero_iff.mpr a.ne_zero))

/-- The source-positive integer order is locally constant on actual field units. -/
theorem fieldOrderUnits_isLocallyConstant : IsLocallyConstant (fieldOrderUnits F) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro a
  filter_upwards [(units_valuation_isLocallyConstant F).eventually_eq a] with b hb
  apply Multiplicative.toAdd.injective
  rw [fieldOrderUnits_toAdd, fieldOrderUnits_toAdd]
  change -WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
      (ValuativeRel.valuation F (b : F))) =
    -WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
      (ValuativeRel.valuation F (a : F)))
  rw [hb]

/-- The positive normalized norm is locally constant on actual field units. -/
theorem fieldNormUnits_isLocallyConstant : IsLocallyConstant (fieldNormUnits F) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro a
  filter_upwards [(fieldOrderUnits_isLocallyConstant F).eventually_eq a] with b hb
  apply Units.ext
  apply NNReal.eq
  rw [fieldNormUnits_zpow, fieldNormUnits_zpow, hb]

/-- The integer order is continuous for the existing unit-group topology. -/
theorem fieldOrderUnits_continuous : Continuous (fieldOrderUnits F) :=
  (fieldOrderUnits_isLocallyConstant F).continuous

/-- The normalized norm is continuous for the existing unit-group topologies. -/
theorem fieldNormUnits_continuous : Continuous (fieldNormUnits F) :=
  (fieldNormUnits_isLocallyConstant F).continuous

/-- All five conclusions of the unchanged, universe-general topology target. -/
theorem fieldUnitsTopology : FieldUnitsTopologyStatement.{uF} := by
  intro F _ _ _ _
  exact ⟨continuous_residueNormalizedAbsoluteValue F,
    fieldOrderUnits_isLocallyConstant F, fieldOrderUnits_continuous F,
    fieldNormUnits_isLocallyConstant F, fieldNormUnits_continuous F⟩

end Langlands.Plancherel
