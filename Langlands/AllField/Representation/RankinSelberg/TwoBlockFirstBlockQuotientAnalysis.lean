import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockQuotientAnalysis
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockQuotientIntegrationStatement
/-!
# Analytic consequences of first-block quotient disintegration

From the everywhere representative formula for a measurable fiber kernel and its exact
restricted-measure composition identity, derive the Tonelli, absolute-integrability and
Bochner conclusions for the published first-block average. The kernel and the normalized
composition identity are hypotheses of this helper, not conclusions.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient
open Langlands.RankinSelberg.TwoBlockFirstBlockQuotient hiding FirstBlockKernelAnalysisStatement MixedQuotient NormOneRightInvariant analytic_of_comp_eq blockUnipotent_le_mixedSubgroup continuous_determinantOrder continuous_fiberPoint determinantOrder determinantOrder_mk determinantSlice determinant_mixedEmbedding fiberIntegral fiberIntegral_def fiberIntegral_mixedEmbedding_mul fiberIntegral_mixedSubgroup_mul fiberPoint_mem_determinantSlice_iff fiberPoint_mixedEmbedding_mul firstBlockAverage firstBlockAverage_eq_integral_kernel firstBlockAverage_mk isClopen_determinantSlice isClosed_mixedSubgroup measurableSet_determinantSlice mem_determinantSlice mem_mixedSubgroup_iff mem_mixedSubgroup_iff_determinantNorm mem_normOneSubgroup_iff mem_normOneSubgroup_iff_normalizedAbs mixedCoordinates mixedCoordinates_mixedEmbedding mixedEmbedding mixedEmbedding_apply mixedEmbedding_index_one_one mixedEmbedding_index_one_zero mixedEmbedding_index_zero_one mixedEmbedding_index_zero_zero mixedEmbedding_mem mixedEmbedding_mixedCoordinates mixedSubgroup mixedSubgroupEquiv mixedSubgroupEquiv_apply_val mixedSubgroupHomeomorph mixedSubgroup_le_normOneSubgroup mixedSubgroup_le_parabolic normOneRightInvariant_of_isCompatible normOneSubgroup ord_determinant_eq_zero
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt TwoBlockFirstBlockQuotientIntegrationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice rightTranslate_mem_determinantSlice

open _root_.MeasureTheory ProbabilityTheory
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
open scoped ENNReal

universe uF

/-- The published first-block average agrees everywhere with integration against any kernel
having the prescribed representative formula. No integrability assumption is needed. -/
theorem firstBlockAverage_eq_integral_kernel :
    ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
      {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1),
      let T := (⟨⟩ : LocalFieldData F)
      letI := T.topology
      letI := T.valuativeRel
      letI := T.localField
      letI := T.fieldT2
      letI := T.secondCountableTopology
      letI := T.generalLinearTopologicalGroup (t + 1)
      letI := T.generalLinearTopologicalGroup (m 0 + 1)
      letI : MeasurableSpace F := borel F
      letI : BorelSpace F := ⟨rfl⟩
      let AQ := LeftUnipotentQuotient (m 0) F
      let HQ := TwoBlockUnipotentQuotient.BlockQuotient h F
      let LQ := MixedQuotient F h
      letI : MeasurableSpace AQ := borel AQ
      letI : BorelSpace AQ := ⟨rfl⟩
      letI : MeasurableSpace HQ := borel HQ
      letI : BorelSpace HQ := ⟨rfl⟩
      letI : MeasurableSpace LQ := borel LQ
      ∀ (νA : Measure AQ) (hInvariant : NormOneRightInvariant F (m 0) νA)
        (k : ℤ) (κ : Kernel LQ HQ),
        (∀ g : GeneralLinear (t + 1) F, κ (Quotient.mk _ g) =
          Measure.map (fun q => fiberPoint h F q g)
            (νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice T (m 0) k))) →
        ∀ f : HQ → ℂ, Measurable f →
          firstBlockAverage F h νA hInvariant k f = fun q => ∫ z, f z ∂κ q := by
  intro F _ _ _ _ t m h T AQ HQ LQ νA hInvariant k κ hκ f hf
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := T.generalLinearTopologicalGroup (t + 1)
  let := T.generalLinearTopologicalGroup (m 0 + 1)
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  let : MeasurableSpace AQ := borel AQ
  let : BorelSpace AQ := ⟨rfl⟩
  let : MeasurableSpace HQ := borel HQ
  let : BorelSpace HQ := ⟨rfl⟩
  let : MeasurableSpace LQ := borel LQ
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    have hcont : Continuous (fun q : AQ => fiberPoint h F q g) :=
      (continuous_fiberPoint F h).comp (continuous_id.prodMk continuous_const)
    rw [firstBlockAverage_mk, hκ g,
      integral_map hcont.measurable.aemeasurable hf.aestronglyMeasurable]

/-- All analytic conclusions of first-block quotient disintegration for a fixed slice follow
from the exact kernel formula and `κ ∘ₘ νL0 = νHk`. The two base measures may be arbitrary;
for the target theorem they are the zero outer slice and the k-th total slice. -/
def FirstBlockKernelAnalysisStatement : Prop :=
    ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
      {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1),
      let T := (⟨⟩ : LocalFieldData F)
      letI := T.topology
      letI := T.valuativeRel
      letI := T.localField
      letI := T.fieldT2
      letI := T.secondCountableTopology
      letI := T.generalLinearTopologicalGroup (t + 1)
      letI := T.generalLinearTopologicalGroup (m 0 + 1)
      letI : MeasurableSpace F := borel F
      letI : BorelSpace F := ⟨rfl⟩
      let AQ := LeftUnipotentQuotient (m 0) F
      let HQ := TwoBlockUnipotentQuotient.BlockQuotient h F
      let LQ := MixedQuotient F h
      letI : MeasurableSpace AQ := borel AQ
      letI : BorelSpace AQ := ⟨rfl⟩
      letI : MeasurableSpace HQ := borel HQ
      letI : BorelSpace HQ := ⟨rfl⟩
      letI : MeasurableSpace LQ := borel LQ
      ∀ (νA : Measure AQ) (hInvariant : NormOneRightInvariant F (m 0) νA)
        (k : ℤ) (κ : Kernel LQ HQ),
        (∀ g : GeneralLinear (t + 1) F, κ (Quotient.mk _ g) =
          Measure.map (fun q => fiberPoint h F q g)
            (νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice T (m 0) k))) →
        ∀ (νL0 : Measure LQ) (νHk : Measure HQ), κ ∘ₘ νL0 = νHk →
          (∀ f : HQ → ℝ≥0∞, Measurable f →
            (∫⁻ q, ∫⁻ z, f z ∂κ q ∂νL0) = ∫⁻ z, f z ∂νHk) ∧
          (∀ f : HQ → ℂ, Measurable f →
            (Integrable f νHk ↔
              (∀ᵐ q ∂νL0, Integrable f (κ q)) ∧
              Integrable (fun q => ∫ z, ‖f z‖ ∂κ q) νL0) ∧
            (Integrable f νHk →
              Integrable (firstBlockAverage F h νA hInvariant k f) νL0 ∧
              (∫ z, f z ∂νHk) =
                ∫ q, firstBlockAverage F h νA hInvariant k f q ∂νL0))

/-- The conditional analytic statement follows from the representative formula and exact
measure composition, using the general integration theorems for measurable kernels. -/
theorem analytic_of_comp_eq : FirstBlockKernelAnalysisStatement.{uF} := by
  intro F _ _ _ _ t m h T AQ HQ LQ νA hInvariant k κ hκ νL0 νHk hκν
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := T.generalLinearTopologicalGroup (t + 1)
  let := T.generalLinearTopologicalGroup (m 0 + 1)
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  let : MeasurableSpace AQ := borel AQ
  let : BorelSpace AQ := ⟨rfl⟩
  let : MeasurableSpace HQ := borel HQ
  let : BorelSpace HQ := ⟨rfl⟩
  let : MeasurableSpace LQ := borel LQ
  refine ⟨fun f hf => ?_, fun f hf => ⟨?_, ?_⟩⟩
  · rw [← hκν, Measure.lintegral_bind κ.measurable.aemeasurable hf.aemeasurable]
  · rw [← hκν]
    exact Measure.integrable_comp_iff hf.aestronglyMeasurable
  · intro hfi
    rw [firstBlockAverage_eq_integral_kernel F h νA hInvariant k κ hκ f hf]
    have hfi' : Integrable f (κ ∘ₘ νL0) := hκν ▸ hfi
    rw [Measure.comp_eq_comp_const_apply] at hfi'
    refine ⟨by simpa using hfi'.integral_comp, ?_⟩
    rw [← hκν, Measure.comp_eq_comp_const_apply, Kernel.integral_comp hfi']
    rfl

end Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient
