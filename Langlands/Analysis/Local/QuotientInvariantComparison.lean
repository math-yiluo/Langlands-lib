import Langlands.Analysis.Local.QuotientPositiveLifting
import Langlands.Analysis.Local.QuotientTranslation
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Comparison of right-invariant measures on actual left quotients

Lift a regular quotient measure to a group measure through the positive real
averaging operator. Haar uniqueness for the inverse lifts and positive lifting
then compare nonzero right-invariant quotient measures by a positive scalar.
-/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure CompactlySupportedContinuousMap
open scoped CompactlySupported NNReal

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (H : Subgroup G) (hH : IsClosed (H : Set G))
variable [MeasurableSpace H] [BorelSpace H]
variable (μH : Measure H) [IsHaarMeasure μH] [μH.Regular] [IsMulRightInvariant μH]
variable [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]

/-- The Riesz measure on the group associated to integration of real
subgroup averages against a supplied quotient measure. -/
def quotientMeasureLift (ν : Measure (LeftQuotient H)) [IsFiniteMeasureOnCompacts ν] :
    Measure G :=
  RealRMK.rieszMeasure
    ((integralPositiveLinearMap ν).comp (quotientAverageRealPositive H hH μH))

instance quotientMeasureLift_regular (ν : Measure (LeftQuotient H))
    [IsFiniteMeasureOnCompacts ν] : (quotientMeasureLift H hH μH ν).Regular := by
  unfold quotientMeasureLift
  infer_instance

omit [μH.Regular] in
/-- The lift integrates a compact test function by integration of its actual
subgroup average against the original quotient measure. -/
theorem integral_quotientMeasureLift (ν : Measure (LeftQuotient H))
    [IsFiniteMeasureOnCompacts ν] (f : C_c(G, ℝ)) :
    (∫ g, f g ∂quotientMeasureLift H hH μH ν) =
      ∫ q, quotientAverageRealPositive H hH μH f q ∂ν := by
  rw [quotientMeasureLift, RealRMK.integral_rieszMeasure]
  rfl

omit [μH.Regular] in
/-- Invariance on the actual quotient lifts to right invariance on the group. -/
theorem quotientMeasureLift_rightInvariant (ν : Measure (LeftQuotient H))
    [IsFiniteMeasureOnCompacts ν]
    (hν : ∀ g : G, MeasurePreserving (rightTranslate H g) ν ν) :
    (quotientMeasureLift H hH μH ν).IsMulRightInvariant := by
  let := leftQuotient_t2Space H hH
  constructor
  intro g
  have : (Measure.map (fun x => x * g) (quotientMeasureLift H hH μH ν)).Regular :=
    Measure.Regular.map (Homeomorph.mulRight g)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  change (∫ x, f x ∂Measure.map (Homeomorph.mulRight g).toMeasurableEquiv
    (quotientMeasureLift H hH μH ν)) = _
  rw [integral_map_equiv (Homeomorph.mulRight g).toMeasurableEquiv (fun x => f x)]
  change (∫ x, compactRightTranslate g f x ∂quotientMeasureLift H hH μH ν) = _
  rw [integral_quotientMeasureLift, integral_quotientMeasureLift]
  simp_rw [compactAveraging_rightTranslate H μH (quotientAverageRealPositive H hH μH)
    (fun f x => rfl) g f]
  exact (hν g).integral_comp (rightTranslate H g).toMeasurableEquiv.measurableEmbedding _

/-- Positive lifting of compact tests ensures that a nonzero regular quotient
measure gives a nonzero group lift. -/
theorem quotientMeasureLift_ne_zero (ν : Measure (LeftQuotient H)) [ν.Regular]
    (hν : ν ≠ 0) : quotientMeasureLift H hH μH ν ≠ 0 := by
  let := leftQuotient_t2Space H hH
  let := leftQuotient_locallyCompactSpace H
  obtain ⟨φ, hφ⟩ := exists_compact_integral_ne_zero ν hν
  obtain ⟨f, hf, _⟩ := realQuotientPositiveLifting H hH μH φ
  have havg : quotientAverageRealPositive H hH μH f = φ := by
    ext q
    induction q using Quotient.inductionOn with
    | h g => exact hf g
  intro hzero
  have h := integral_quotientMeasureLift H hH μH ν f
  rw [hzero, integral_zero_measure, havg] at h
  exact hφ h.symm

include hH μH in
/-- Two regular nonzero measures on the actual left quotient that are
invariant under every right translation differ by a positive finite real
scalar. The ambient group need not be unimodular. -/
theorem exists_pos_smul_eq_of_rightInvariant_quotient
    (ν₁ ν₂ : Measure (LeftQuotient H)) [ν₁.Regular] [ν₂.Regular]
    (hν₁ : ν₁ ≠ 0) (hν₂ : ν₂ ≠ 0)
    (hinv₁ : ∀ g : G, MeasurePreserving (rightTranslate H g) ν₁ ν₁)
    (hinv₂ : ∀ g : G, MeasurePreserving (rightTranslate H g) ν₂ ν₂) :
    ∃ C : ℝ, 0 < C ∧ ν₁ = ENNReal.ofReal C • ν₂ := by
  let := leftQuotient_t2Space H hH
  let := leftQuotient_locallyCompactSpace H
  let M₁ := quotientMeasureLift H hH μH ν₁
  let M₂ := quotientMeasureLift H hH μH ν₂
  have : M₁.IsMulRightInvariant := quotientMeasureLift_rightInvariant H hH μH ν₁ hinv₁
  have : M₂.IsMulRightInvariant := quotientMeasureLift_rightInvariant H hH μH ν₂ hinv₂
  have hM₁ : M₁ ≠ 0 := quotientMeasureLift_ne_zero H hH μH ν₁ hν₁
  have hM₂ : M₂ ≠ 0 := quotientMeasureLift_ne_zero H hH μH ν₂ hν₂
  have : NeZero M₁.inv := ⟨by
    intro h
    apply hM₁
    calc
      M₁ = M₁.inv.inv := (Measure.inv_inv M₁).symm
      _ = (0 : Measure G).inv := congrArg Measure.inv h
      _ = 0 := by simp [Measure.inv_def]⟩
  have : NeZero M₂.inv := ⟨by
    intro h
    apply hM₂
    calc
      M₂ = M₂.inv.inv := (Measure.inv_inv M₂).symm
      _ = (0 : Measure G).inv := congrArg Measure.inv h
      _ = 0 := by simp [Measure.inv_def]⟩
  have : M₁.inv.IsHaarMeasure := {
    toIsMulLeftInvariant := inferInstance
    toIsFiniteMeasureOnCompacts := inferInstance
    toIsOpenPosMeasure := inferInstance }
  have : M₂.inv.IsHaarMeasure := {
    toIsMulLeftInvariant := inferInstance
    toIsFiniteMeasureOnCompacts := inferInstance
    toIsOpenPosMeasure := inferInstance }
  let c : ℝ≥0 := haarScalarFactor M₁.inv M₂.inv
  have hc : 0 < c := haarScalarFactor_pos_of_isHaarMeasure M₁.inv M₂.inv
  have hinv : M₁.inv = c • M₂.inv :=
    isMulLeftInvariant_eq_smul_of_regular M₁.inv M₂.inv
  have hM : M₁ = c • M₂ := by
    calc
      M₁ = M₁.inv.inv := (Measure.inv_inv M₁).symm
      _ = (c • M₂.inv).inv := congrArg Measure.inv hinv
      _ = c • M₂ := by
        rw [Measure.inv_def, Measure.map_smul c measurable_inv.aemeasurable,
          ← Measure.inv_def, Measure.inv_inv]
  have hν : ν₁ = c • ν₂ := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro φ
    obtain ⟨f, hf, _⟩ := realQuotientPositiveLifting H hH μH φ
    have havg : quotientAverageRealPositive H hH μH f = φ := by
      ext q
      induction q using Quotient.inductionOn with
      | h g => exact hf g
    have hi := congrArg (fun M : Measure G => ∫ x, f x ∂M) hM
    change (∫ x, f x ∂quotientMeasureLift H hH μH ν₁) =
      ∫ x, f x ∂(c • quotientMeasureLift H hH μH ν₂) at hi
    rw [integral_smul_nnreal_measure, integral_quotientMeasureLift,
      integral_quotientMeasureLift, havg] at hi
    simpa only [integral_smul_nnreal_measure] using hi
  refine ⟨c, by exact_mod_cast hc, ?_⟩
  simpa only [ENNReal.ofReal_coe_nnreal, ← ENNReal.smul_def] using hν

end Langlands.QuotientIntegration
