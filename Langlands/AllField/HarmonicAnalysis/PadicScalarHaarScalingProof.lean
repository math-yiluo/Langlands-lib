import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
import Langlands.AllField.HarmonicAnalysis.PadicHaarScalingStatement
/-!
# Residue-normalized scalar Haar scaling

Intrinsic topology and regularity lemmas for a supplied local-field realization,
followed by the scalar pushforward formula for every additive Haar measure.
-/

open scoped NNReal ENNReal Pointwise
open MeasureTheory Set TopologicalSpace

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData
universe uF
variable {F : Type uF} [Field F] (T : LocalFieldData F)

private theorem residueCardinality_mul_measure_maximalIdeal :
    letI := T.topology
    ∀ [MeasurableSpace F] [BorelSpace F]
      (μ : Measure F) [μ.IsAddHaarMeasure],
      (T.residueCardinality : ℝ≥0∞) *
        μ (Subtype.val '' (IsLocalRing.maximalIdeal T.Integers : Set T.Integers)) =
      μ (T.Integers : Set F) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ _ μ _
  let := T.fieldT2
  let := T.finite_residueField
  let H := (IsLocalRing.maximalIdeal T.Integers).toAddSubgroup
  have hme : MeasurableEmbedding (Subtype.val : T.Integers → F) :=
    MeasurableEmbedding.subtype_coe T.isOpen_integers.measurableSet
  let ν := μ.comap (T.Integers.subtype : T.Integers →+* F)
  have : ν.IsAddLeftInvariant := Measure.IsAddLeftInvariant.comap μ
    (f := T.Integers.subtype.toAddMonoidHom) hme
  have : H.FiniteIndex := @AddSubgroup.finiteIndex_of_finite_quotient _ _ H T.finite_residueField
  have hH : MeasurableSet (H : Set T.Integers) :=
    (IsLocalRing.isOpen_maximalIdeal T.Integers).measurableSet
  have he := H.index_mul_measure hH ν
  change (T.residueCardinality : ℝ≥0∞) * ν H = ν Set.univ at he
  change (T.residueCardinality : ℝ≥0∞) *
    (μ.comap (Subtype.val : T.Integers → F)) (H : Set T.Integers) =
    (μ.comap (Subtype.val : T.Integers → F)) Set.univ at he
  have hrange : Set.range (Subtype.val : T.Integers → F) =
      (T.Integers : Set F) := Set.ext (fun x => by simp)
  simpa only [hme.comap_apply, Set.image_univ, hrange, H, Submodule.coe_toAddSubgroup] using he

private theorem smul_integers_eq (a : Fˣ) :
    a • (T.Integers : Set F) = {x | T.normalizedAbs x ≤ T.normalizedAbs a} := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  change (↑a⁻¹ : F) * x ∈ T.Integers ↔ _
  rw [← T.normalizedAbs_le_one_iff_mem_integers, T.normalizedAbs_mul]
  have hinv : T.normalizedAbs (↑a⁻¹ : F) = (T.normalizedAbs a)⁻¹ := by
    simpa only [normalizedAbsHom_coe, Units.val_inv_eq_inv_val, NNReal.coe_inv] using
      congrArg (fun x : ℝ≥0 => (x : ℝ)) (map_inv₀ T.normalizedAbsHom (a : F))
  rw [hinv, inv_mul_le_iff₀ (T.normalizedAbs_pos a.ne_zero), mul_one]
  rfl

private theorem uniformizer_ne_zero : T.uniformizer ≠ 0 := by
  intro h
  have ho := T.ord_uniformizer
  rw [h, T.ord_zero] at ho
  exact zero_ne_one ho

private theorem uniformizer_smul_integers :
    (Units.mk0 T.uniformizer T.uniformizer_ne_zero) • (T.Integers : Set F) =
      Subtype.val '' (IsLocalRing.maximalIdeal T.Integers : Set T.Integers) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let v := ValuativeRel.valuation F
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  have hstep (x : F) : T.discreteValuation x ≤ WithZero.exp (-1) ↔ v x < 1 := by
    have h := WithZero.lt_mul_exp_iff_le (x := T.discreteValuation x)
      (y := WithZero.exp (-1)) WithZero.exp_ne_zero
    have he : T.discreteValuation x < 1 ↔ v x < 1 := by
      change e (v x) < 1 ↔ v x < 1
      rw [← map_one e, e.strictMono.lt_iff_lt]
    simpa [← WithZero.exp_add, he] using h.symm
  rw [T.smul_integers_eq]
  ext x
  have hleft : T.normalizedAbs x ≤ T.normalizedAbs T.uniformizer ↔ v x < 1 := by
    by_cases hx : x = 0
    · subst x
      simp [T.normalizedAbs_zero, (T.normalizedAbs_pos T.uniformizer_ne_zero).le]
    rw [T.normalizedAbs_le_iff_of_ne_zero hx T.uniformizer_ne_zero,
      T.discreteValuation_uniformizer, hstep]
  change T.normalizedAbs x ≤ T.normalizedAbs T.uniformizer ↔ _
  rw [hleft]
  constructor
  · intro hx
    have hxO : x ∈ T.Integers := hx.le
    refine ⟨⟨x, hxO⟩, ?_, rfl⟩
    change (⟨x, hxO⟩ : T.Integers) ∈ IsLocalRing.maximalIdeal T.Integers
    rw [IsLocalRing.mem_maximalIdeal]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr hx
  · rintro ⟨x, hx, rfl⟩
    change x ∈ IsLocalRing.maximalIdeal T.Integers at hx
    rw [IsLocalRing.mem_maximalIdeal] at hx
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hx

private theorem distribHaarChar_eq_normalizedAbsUnits :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [MeasurableSpace F] [BorelSpace F]
      (μ : Measure F) [μ.IsAddHaarMeasure] (a : Fˣ),
      distribHaarChar F a = (T.normalizedAbsUnits a : ℝ≥0) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ _ μ _ a
  let := T.haarMeasure_regular μ
  have hO0 : μ (T.Integers : Set F) ≠ 0 :=
    ne_of_gt (T.isOpen_integers.measure_pos μ ⟨0, T.Integers.zero_mem⟩)
  have hOtop : μ (T.Integers : Set F) ≠ ∞ :=
    T.isCompact_integers.measure_ne_top
  let π : Fˣ := Units.mk0 T.uniformizer T.uniformizer_ne_zero
  have hπ : distribHaarChar F π = (T.residueCardinality : ℝ≥0)⁻¹ := by
    have h := T.residueCardinality_mul_measure_maximalIdeal μ
    rw [← T.uniformizer_smul_integers, ← distribHaarChar_mul μ] at h
    have hp : (T.residueCardinality : ℝ≥0∞) * ↑(distribHaarChar F π) = 1 := by
      apply (ENNReal.mul_left_inj hO0 hOtop).mp
      simpa only [mul_assoc, one_mul] using h
    have hp' : (T.residueCardinality : ℝ≥0) * distribHaarChar F π = 1 := by
      exact ENNReal.coe_injective (by simpa only [ENNReal.coe_mul, ENNReal.coe_natCast,
        ENNReal.coe_one] using hp)
    have hq0 : (T.residueCardinality : ℝ≥0) ≠ 0 := by
      exact_mod_cast (lt_trans Nat.zero_lt_one T.residueCardinality_gt_one).ne'
    apply mul_left_cancel₀ hq0
    rw [mul_inv_cancel₀ hq0]
    exact hp'
  have habs : T.normalizedAbs ((π ^ T.ord a : Fˣ) : F) =
      T.normalizedAbs a := by
    rw [T.normalizedAbs_of_ne_zero (π ^ T.ord a).ne_zero,
      T.normalizedAbs_of_ne_zero a.ne_zero]
    simp only [Units.val_zpow_eq_zpow_val, T.ord_zpow, π, Units.val_mk0,
      T.ord_uniformizer, mul_one]
  have hchar : distribHaarChar F a = distribHaarChar F (π ^ T.ord a) := by
    apply ENNReal.coe_injective
    apply (ENNReal.mul_left_inj hO0 hOtop).mp
    rw [distribHaarChar_mul μ, distribHaarChar_mul μ,
      T.smul_integers_eq, T.smul_integers_eq, habs]
  rw [hchar, map_zpow, hπ]
  apply NNReal.eq
  rw [NNReal.coe_zpow, NNReal.coe_inv, NNReal.coe_natCast, T.normalizedAbsUnits_coe,
    T.normalizedAbs_of_ne_zero a.ne_zero, inv_zpow, zpow_neg]

end Langlands.LocalFieldData

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF

/-- Scalar pushforward of any additive Haar measure, using the supplied
residue-normalized absolute value and deriving regularity intrinsically. -/
theorem padicScalarHaarScaling (F : Type uF) [Field F]
    (T : LocalFieldData F) :
    letI := T.topology
    ∀ [MeasurableSpace F] [BorelSpace F]
      (μ : Measure F) [μ.IsAddHaarMeasure] (a : Fˣ),
      μ.map (fun x => (a : F) * x) =
        ((T.normalizedAbsUnits a : ℝ≥0)⁻¹) • μ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ _ μ _ a
  let := T.haarMeasure_regular μ
  ext s hs
  change (μ.map (fun x => a • x)) s = _
  rw [Measure.map_apply (measurable_const_smul a) hs, Set.preimage_smul,
    ← distribHaarChar_mul μ, T.distribHaarChar_eq_normalizedAbsUnits μ,
    map_inv, Units.val_inv_eq_inv_val, Measure.smul_apply]
  rfl

end Langlands.AllField.HarmonicAnalysis
