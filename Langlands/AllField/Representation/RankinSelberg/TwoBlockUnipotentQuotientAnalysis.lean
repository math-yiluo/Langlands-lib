import Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientAnalysis
import Langlands.AllField.Representation.RankinSelberg.TwoBlockUnipotentQuotientIntegrationStatement
/-!
# Analytic consequences of a scaled kernel tower

Support for the proof of `TwoBlockUnipotentQuotientIntegrationStatement` (JPSS (1983),
Section 4.6, printed pages 411-412). From a measurable s-finite kernel `κ` from
`N \ GL_(t+1)` to `H \ GL_(t+1)` whose value at `[g]_N` is the pushforward of a rectangular
measure along the radical fiber map, and from a scaled identity `κ ∘ₘ ν_N = c • ν_H` with
`0 < c < ∞`, this module derives the nonnegative Tonelli identity, the characterization of
absolute integrability, and the integrability and Bochner formula for the actual
`radicalAverage`. The kernel and the measure identity are hypotheses here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient
open Langlands.RankinSelberg.TwoBlockUnipotentQuotient hiding analytic_of_comp_eq_smul continuous_fiberPoint continuous_projection determinantSlice fiberIntegral fiberIntegral_def fiberIntegral_upperUnipotent_mul isClopen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice radicalAverage radicalAverage_eq_integral_kernel radicalAverage_mk
open Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt TwoBlockUnipotentQuotientIntegrationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg hiding determinantSlice iUnion_determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice pairwise_disjoint_determinantSlice

open Langlands.GeneralLinear hiding blockUnipotent
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet

universe uF

/-! ### Scaled kernel towers on arbitrary measurable spaces -/

section Generic


end Generic

/-! ### The radical average as a kernel integral -/

/-- If the kernel value at every `[g]_N` is the pushforward of `μR` along the radical fiber
map `x ↦ [u(x) g]_H`, then the actual radical average of a measurable function is its
kernel integral at every point of `N \ GL_(t+1)`. -/
theorem radicalAverage_eq_integral_kernel :
    ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
      {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1),
      let T := (⟨⟩ : LocalFieldData F)
      letI := T.topology
      letI := T.valuativeRel
      letI := T.localField
      letI := T.fieldT2
      letI := T.secondCountableTopology
      letI := T.generalLinearTopologicalGroup (t + 1)
      letI : MeasurableSpace F := borel F
      letI : BorelSpace F := ⟨rfl⟩
      let NQ := LeftUnipotentQuotient t F
      let HQ := BlockQuotient h F
      let R := Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F
      letI : MeasurableSpace NQ := borel NQ
      letI : MeasurableSpace HQ := borel HQ
      letI : BorelSpace HQ := ⟨rfl⟩
      ∀ (μR : Measure R) [μR.IsAddHaarMeasure] (κ : Kernel NQ HQ),
        (∀ g : GeneralLinear (t + 1) F, κ (Quotient.mk _ g) =
          Measure.map (fun x => fiberPoint h F x g) μR) →
        ∀ f : HQ → ℂ, Measurable f →
          radicalAverage F h μR f = fun q => ∫ z, f z ∂κ q := by
  intro F _ _ _ _ t m h T NQ HQ R μR _ κ hκ f hf
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := T.generalLinearTopologicalGroup (t + 1)
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  let : MeasurableSpace NQ := borel NQ
  let : MeasurableSpace HQ := borel HQ
  let : BorelSpace HQ := ⟨rfl⟩
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    have hcont : Continuous (fun x : R => fiberPoint h F x g) :=
      continuous_quotient_mk'.comp ((continuous_upperRadical h F).mul continuous_const)
    rw [radicalAverage_mk, hκ g,
      integral_map hcont.measurable.aemeasurable hf.aestronglyMeasurable]

/-! ### The analytic conclusions of the two-block tower -/

/-- The analytic conjuncts of `TwoBlockUnipotentQuotientIntegrationStatement`, for one
restricted pair `ν_N|_s`, `ν_H|_(π⁻¹ s)`, from an s-finite kernel with the radical fiber law
and the scaled restricted identity `κ ∘ₘ ν_N|_s = c • ν_H|_(π⁻¹ s)` with `0 < c < ∞`.
The two restricted measures are arbitrary here; `ν_N|_s` is assumed s-finite. -/
theorem analytic_of_comp_eq_smul :
    ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
      {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1),
      let T := (⟨⟩ : LocalFieldData F)
      letI := T.topology
      letI := T.valuativeRel
      letI := T.localField
      letI := T.fieldT2
      letI := T.secondCountableTopology
      letI := T.generalLinearTopologicalGroup (t + 1)
      letI : MeasurableSpace F := borel F
      letI : BorelSpace F := ⟨rfl⟩
      let NQ := LeftUnipotentQuotient t F
      let HQ := BlockQuotient h F
      let R := Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F
      letI : MeasurableSpace NQ := borel NQ
      letI : MeasurableSpace HQ := borel HQ
      letI : BorelSpace HQ := ⟨rfl⟩
      ∀ (μR : Measure R) [μR.IsAddHaarMeasure] (c : ℝ≥0∞), c ≠ 0 → c ≠ ⊤ →
      ∀ (κ : Kernel NQ HQ) [IsSFiniteKernel κ],
        (∀ g : GeneralLinear (t + 1) F, κ (Quotient.mk _ g) =
          Measure.map (fun x => fiberPoint h F x g) μR) →
      ∀ (νNs : Measure NQ) [SFinite νNs] (νHs : Measure HQ), κ ∘ₘ νNs = c • νHs →
        (∀ f : HQ → ℝ≥0∞, Measurable f →
          (∫⁻ q, ∫⁻ z, f z ∂κ q ∂νNs) = c * ∫⁻ z, f z ∂νHs) ∧
        (∀ f : HQ → ℂ, Measurable f →
          (Integrable f νHs ↔
            (∀ᵐ q ∂νNs, Integrable f (κ q)) ∧
            Integrable (fun q => ∫ z, ‖f z‖ ∂κ q) νNs) ∧
          (Integrable f νHs →
            Integrable (radicalAverage F h μR f) νNs ∧
            (∫ q, radicalAverage F h μR f q ∂νNs) =
              c.toReal • (∫ z, f z ∂νHs))) := by
  intro F _ _ _ _ t m h T NQ HQ R μR _ c hc0 hc κ _ hκ νNs _ νHs hκν
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := T.generalLinearTopologicalGroup (t + 1)
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  let : MeasurableSpace NQ := borel NQ
  let : MeasurableSpace HQ := borel HQ
  let : BorelSpace HQ := ⟨rfl⟩
  refine ⟨fun f hf => lintegral_lintegral_of_comp_eq_smul hκν hf, fun f hf => ⟨?_, ?_⟩⟩
  · exact integrable_iff_of_comp_eq_smul hκν hc0 hc hf.aestronglyMeasurable
  · intro hfi
    rw [radicalAverage_eq_integral_kernel F h μR κ hκ f hf]
    exact integral_integral_of_comp_eq_smul hκν hc hfi

end Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient
