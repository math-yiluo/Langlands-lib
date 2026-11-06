import Langlands.Global.PositiveQuotientL2UnfoldingStatement
import Langlands.Analysis.Local.QuotientL2UnfoldingProof

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme AdelicGroupPoints Langlands.QuotientIntegration

/-- Compact averaging and absolute L² unfolding on the actual positive quotient. -/
theorem positiveQuotientL2Unfolding : PositiveQuotientL2UnfoldingStatement.{u} := by
  intro F _ _ G T i _ _ hi _ I _ e hc _ f
  let Γ := rationalNormOneSubgroup F G
  have hd : IsDiscrete (Γ : Set (normOneSubgroup F G)) :=
    isDiscrete_rationalNormOneSubgroup F G
  have hcl : IsClosed (Γ : Set (normOneSubgroup F G)) := Γ.isClosed_of_isDiscrete hd
  let : Countable Γ := LeftCosetSpace.countable_of_isDiscrete Γ hd
  let : IsFiniteMeasureOnCompacts (Measure.count : Measure Γ) :=
    LeftCosetSpace.isFiniteMeasureOnCompacts_count Γ hd
  let := positiveRationalQuotient_borelSpace F G T i hi I e hc
  let := positiveRationalQuotient_t2Space F G T i hi I e hc
  let := positiveRationalQuotientHaarMeasure_isLocallyFiniteMeasure F G T i hi I e hc
  obtain ⟨hncont, hncompact, -⟩ := quotientL2Unfolding Γ hcl Measure.count Measure.haar
    (normOneRationalQuotientHaarMeasure F G)
    (normOneRationalQuotientHaarMeasure_isCompatible F G) f
  let A := positiveNormOneQuotientAverage F G T i hi I e hc f
  have hcont : Continuous A :=
    hncont.comp (positiveQuotientHomeomorph F G T i hi I e hc).symm.continuous
  have hcompact : HasCompactSupport A :=
    hncompact.comp_homeomorph (positiveQuotientHomeomorph F G T i hi I e hc).symm
  have hLp : MemLp A 2 (positiveRationalQuotientHaarMeasure F G T i) :=
    hcont.memLp_of_hasCompactSupport hcompact
  let v := hLp.toLp A
  have hv : (v : PositiveRationalQuotient F G T i → ℂ) =ᵐ[
      positiveRationalQuotientHaarMeasure F G T i] A := hLp.coeFn_toLp
  refine ⟨hcont, hcompact, v, innerSL ℂ v, hv, ?_⟩
  intro φ
  let ψ : NormOneRationalQuotient F G → ℂ :=
    fun q => φ (normOneToPositiveQuotient F G T i q)
  have hψm : StronglyMeasurable ψ :=
    (Lp.stronglyMeasurable φ).comp_measurable
      (positiveQuotientMeasurableEquiv F G T i hi I e hc).measurable
  have hψ : MemLp ψ 2 (normOneRationalQuotientHaarMeasure F G) :=
    (Lp.memLp φ).comp_measurePreserving
      (measurePreserving_positiveQuotient F G T i hi I e hc)
  obtain ⟨hF, hunfold⟩ := integrable_compact_quotient_unfolding Γ hcl Measure.count
    Measure.haar (normOneRationalQuotientHaarMeasure F G)
    (normOneRationalQuotientHaarMeasure_isCompatible F G) f ψ hψm hψ
  refine ⟨hF, innerSL_apply_apply ℂ v φ, ?_⟩
  calc
    inner ℂ v φ = ∫ q, star (A q) * φ q ∂positiveRationalQuotientHaarMeasure F G T i := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hv] with q hq
      simp only [hq, RCLike.inner_apply', starRingEnd_apply]
    _ = ∫ q, star (quotientAverage Γ Measure.count f q) * ψ q
        ∂normOneRationalQuotientHaarMeasure F G := by
      rw [integral_positiveRationalQuotientHaarMeasure F G T i hi I e hc]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun q => by
        simp only [A, positiveNormOneQuotientAverage_normOneToPositiveQuotient, ψ, Γ]
    _ = _ := hunfold.symm

end Langlands.Global.PositiveRealTorus
