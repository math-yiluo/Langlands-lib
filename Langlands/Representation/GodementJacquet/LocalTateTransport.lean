import Langlands.Representation.GodementJacquet.TateScalarFunctionalEquation

/-! Scalar coordinates and normalized rank-one Haar transport over arbitrary local fields. -/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis RankinSelberg GeneralLinear
open scoped NNReal ENNReal

universe uF

section Coordinates

variable (F : Type uF) [Field F] [TopologicalSpace F] [IsTopologicalRing F]

/-- The actual rank-one unipotent quotient in scalar coordinates. -/
def tateScalarQuotientHomeomorph : Fˣ ≃ₜ LeftUnipotentQuotient 0 F :=
  (tateScalarEquiv F).toHomeomorph.trans rankOneQuotientHomeomorph.symm

@[simp] theorem tateScalarQuotientHomeomorph_apply (a : Fˣ) :
    tateScalarQuotientHomeomorph F a = Quotient.mk _ (tateScalarEquiv F a) := rfl

end Coordinates

section LocalField

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [T2Space F]
  [MeasurableSpace Fˣ] [BorelSpace Fˣ]
  [MeasurableSpace (Langlands.GeneralLinear 1 F)] [BorelSpace (Langlands.GeneralLinear 1 F)]

/-- The scalar isomorphism preserves the two normalized Haar measures over every
nonarchimedean local field. Regular Haar uniqueness avoids countability premises. -/
theorem tateScalarEquiv_measurePreserving :
    MeasurePreserving (tateScalarEquiv F)
      (localMultiplicativeHaar F) (generalLinearHaar F 0) := by
  let e := tateScalarEquiv F
  let μ := localMultiplicativeHaar F
  let K := Conductor.levelOpenSubgroup F 0 0
  let : LocallyCompactSpace (Langlands.GeneralLinear 1 F) :=
    e.toHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  have : (μ.map e).IsHaarMeasure := e.isHaarMeasure_map μ
  have : (μ.map e).Regular := Measure.Regular.map e.toHomeomorph
  have hpre : e ⁻¹' (K : Set (Langlands.GeneralLinear 1 F)) =
      (integralUnits (ValuativeRel.valuation F).integer : Set Fˣ) := by
    ext a
    change e a ∈ Conductor.levelSubgroup F 0 0 ↔ _
    rw [Conductor.levelSubgroup_zero]
    exact tateScalarEquiv_mem_integral F _ a
  have hm : μ.map e (K : Set (Langlands.GeneralLinear 1 F)) = 1 := by
    rw [Measure.map_apply (f := fun a => e a)
      e.continuous_toFun.measurable K.isOpen.measurableSet, hpre]
    exact localMultiplicativeHaar_integerUnits F
  have hK : generalLinearHaar F 0 (K : Set (Langlands.GeneralLinear 1 F)) = 1 :=
    normalizedCompactOpenHaar_self _ _
  have heq := Measure.isMulLeftInvariant_eq_smul_of_regular
    (μ.map e) (generalLinearHaar F 0)
  have hc : Measure.haarScalarFactor (μ.map e) (generalLinearHaar F 0) = 1 := by
    have h := congrArg (fun ν : Measure (Langlands.GeneralLinear 1 F) => ν K) heq
    have hcoe : ((Measure.haarScalarFactor (μ.map e) (generalLinearHaar F 0) : ℝ≥0) : ℝ≥0∞) = 1 := by
      simpa [Measure.smul_apply, hm, hK] using h.symm
    exact_mod_cast hcoe
  refine ⟨e.continuous.measurable, ?_⟩
  simpa only [hc, one_smul] using heq

/-- Integrability transports with no measure rescaling or characteristic restriction. -/
theorem integrable_tateScalarEquiv_iff (A : Langlands.GeneralLinear 1 F → ℂ) :
    Integrable (fun a => A (tateScalarEquiv F a)) (localMultiplicativeHaar F) ↔
      Integrable A (generalLinearHaar F 0) :=
  (tateScalarEquiv_measurePreserving F).integrable_comp_emb
    (tateScalarEquiv F).toHomeomorph.measurableEmbedding

/-- Totalized complex integrals transport along the actual scalar isomorphism. -/
theorem integral_tateScalarEquiv (A : Langlands.GeneralLinear 1 F → ℂ) :
    (∫ a, A (tateScalarEquiv F a) ∂localMultiplicativeHaar F) =
      ∫ g, A g ∂generalLinearHaar F 0 :=
  (tateScalarEquiv_measurePreserving F).integral_comp
    (tateScalarEquiv F).toHomeomorph.measurableEmbedding A

variable [MeasurableSpace (LeftUnipotentQuotient 0 F)]
  [BorelSpace (LeftUnipotentQuotient 0 F)]

/-- The scalar coordinate map preserves the actual quotient Haar measure. -/
theorem tateScalarQuotientHomeomorph_measurePreserving :
    MeasurePreserving (tateScalarQuotientHomeomorph F)
      (localMultiplicativeHaar F) (rankOneQuotientHaar F) := by
  have hquot : MeasurePreserving rankOneQuotientHomeomorph.symm
      (generalLinearHaar F 0) (rankOneQuotientHaar F) :=
    ⟨rankOneQuotientHomeomorph.symm.continuous.measurable, rfl⟩
  exact hquot.comp (tateScalarEquiv_measurePreserving F)

/-- Every actual complex quotient integral is the scalar integral in these coordinates. -/
theorem integral_tateScalarQuotientHomeomorph (A : LeftUnipotentQuotient 0 F → ℂ) :
    (∫ a, A (tateScalarQuotientHomeomorph F a) ∂localMultiplicativeHaar F) =
      ∫ x, A x ∂rankOneQuotientHaar F :=
  (tateScalarQuotientHomeomorph_measurePreserving F).integral_comp
    (tateScalarQuotientHomeomorph F).measurableEmbedding A

end LocalField

end Langlands.GodementJacquet
