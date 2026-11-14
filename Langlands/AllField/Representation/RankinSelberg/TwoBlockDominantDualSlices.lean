import Langlands.Representation.RankinSelberg.TwoBlockDominantDualSlices
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantDualKernel
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantSliceSpectral
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFourierMeasure
/-!
# Actual dominant determinant slices under reversed duality

The matrix comparison remains an explicit premise. Every quotient measure is
the exact lower transport of the supplied compatible standard measure.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg.TwoBlockDominantRectangular hiding AbsoluteInput FiberIntegrable KernelAbsoluteIntegrable KernelNormProfileIntegrable KernelOuterIntegrable NormProfileIntegrable OuterIntegrable absoluteInput_standard_iff ae_lowerQuotientMeasure_iff ae_quotientFiberIntegrable_spectral_iff determinantWeight_lowerBlockUnipotent_mul dualKernelLocalField dualKernelMeasurable dualKernelTopology dualKernelValuation dualRectangleBorel dualRectangleLocalField dualRectangleMatrixBorel dualRectangleMatrixSecondCountable dualRectangleMeasurable dualRectangleProductBorel dualRectangleSecondCountable dualRectangleTopology dualRectangleValuation dualSlicesGLBorel dualSlicesGLMeasurable dualSlicesGLTopologicalGroup dualSlicesLocalField dualSlicesLowerBorel dualSlicesLowerMeasurable dualSlicesMeasurable dualSlicesStandardMeasurable dualSlicesTopology dualSlicesUnipotentBorel dualSlicesUnipotentMeasurable dualSlicesValuation fiberIntegrable_lowerBlockUnipotent_mul_iff fiberIntegrable_spectral_iff integrableOn_quotientKernel_spectral_iff integrableOn_quotientNormProfile_spectral_iff integrable_lowerQuotientMeasure_iff integrable_rectangleChange_iff integral_dualRectangleEquiv integral_rectangleChange kernel kernelAbsoluteIntegrable_iff kernelAbsoluteIntegrable_restrict_spectral_iff kernelAbsoluteIntegrable_standard_iff kernelSliceCoefficient kernel_covariance kernel_eq kernel_reversedDual kernel_spectral lowerDuality_restrict_measurePreserving measurePreserving_dualRectangleEquiv measurePreserving_rectangleChange outerFieldT2 outerFieldTopology outerFieldValuation outerGeneralLinearGroup outerGeneralLinearLocallyCompact outerGeneralLinearSecondCountable outerLocalField quotientFiberIntegrable quotientFiberIntegrable_spectral_iff quotientKernel quotientKernelMeasurable quotientKernelTopology quotientKernel_mk quotientKernel_reversedDual quotientKernel_spectral quotientKernel_spectral_onSlice quotientNormProfile quotientNormProfile_mk quotientNormProfile_spectral quotientNormProfile_spectral_onSlice rawKernel rawKernel_covariance rawKernel_reversedDual rawScalarValue rectangleChangeHomeomorph rectangleHaarBorel rectangleHaarLocalField rectangleHaarMeasurable rectangleHaarSecondCountable rectangleHaarTopology rectangleHaarValuation rectangleMatrixBorel rectangleMatrixSecondCountable rectangleMeasure rectangleMeasure_sigmaFinite rectanglesBorel representativeKernel representativeKernel_lowerBlockUnipotent_mul representativeKernel_reversedDual representativeKernel_spectral representativeNormProfile representativeNormProfile_lowerBlockUnipotent_mul representativeNormProfile_spectral reversedDualSectionEquiv reversedDualSectionEquiv_scalar reversedDualSliceCoefficient reversedDualSliceCoefficient_eq setIntegral_quotientKernel_reversedDual setIntegral_quotientKernel_spectral sliceSpectralMeasurable sliceSpectralTopology standardCompatible standardCompatible_sigmaFinite
open Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement EqualRankAnalyticStatement EqualRankContinuedFormsStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt TwoBlockDualSectionJacquetStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankContinuedForms equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockDualSectionJacquet zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.Whittaker hiding TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement padicMatrixFourierSlice padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerFixedSlice hiding compatible_measure_data integrable_lowerMeasure_iff integral_lowerMeasure lowerMeasure lowerMeasure_restrict measureTransportFieldT2 measureTransportFieldTopology measureTransportFieldValuation measureTransportGeneralLinearGroup measureTransportGeneralLinearLocallyCompact measureTransportGeneralLinearSecondCountable measureTransportLocalField sigmaFinite_lowerMeasure
open Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice
open Langlands.QuotientIntegration

universe uF uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i+1) = t+1)
  {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
  [hmod : ∀ i, Module ℂ (W i)]
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i+1) F) (W i))

local instance dualSlicesMeasurable : MeasurableSpace F := borel F
local instance dualSlicesGLTopologicalGroup :
    IsTopologicalGroup (GeneralLinear (t+1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t+1)
local instance dualSlicesGLMeasurable :
    MeasurableSpace (GeneralLinear (t+1) F) := borel _
local instance dualSlicesGLBorel :
    BorelSpace (GeneralLinear (t+1) F) := ⟨rfl⟩
local instance dualSlicesUnipotentMeasurable :
    MeasurableSpace (upperUnipotent (t+1) F) := borel _
local instance dualSlicesUnipotentBorel :
    BorelSpace (upperUnipotent (t+1) F) := ⟨rfl⟩
local instance dualSlicesStandardMeasurable :
    MeasurableSpace (LeftUnipotentQuotient t F) := borel _
local instance dualSlicesLowerMeasurable :
    MeasurableSpace (LowerQuotient h F) := borel _
local instance dualSlicesLowerBorel :
    BorelSpace (LowerQuotient h F) := ⟨rfl⟩

variable (hσ : ∀ i, IsSmooth (σ i))
  (ψ : UnitaryAdditiveCharacter F)
  (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
  {r j k : ℕ} (hr : r=t+(j+k+1))
  (f : Sections F h σ) (Wtest : WhittakerFunctions ψ r)
  (ν : AdditiveHaarMeasure F)
  (νN : Measure (LeftUnipotentQuotient t F))

/-- The actual zero-parameter slice coefficient of the fixed reversed dual
section and the prescribed Weyl-translated dual test. -/
def reversedDualSliceCoefficient (d : ℤ) : ℂ :=
  kernelSliceCoefficient ν
    (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
    (reversedDualSectionEquiv F h σ hσ f) (reversedDualTest hr ψ Wtest)
    νN (by omega : r=t+(k+j+1)) d

variable (hN : Measure.IsMulRightInvariant (unipotentHaar F t))
  (hνN : IsCompatible (upperUnipotent (t+1) F)
    (generalLinearHaar F t) (unipotentHaar F t) νN)

include hN hνN in
omit σ hadd hmod hσ ψ ell hr f Wtest ν in
/-- The published exact measure law in the notation of the actual coefficients. -/
theorem lowerDuality_restrict_measurePreserving (d : ℤ) :
    MeasurePreserving (TwoBlockLowerFourier.lowerDuality F h)
      ((lowerMeasure F h νN).restrict
        (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h d))
      ((lowerMeasure F (reverse_sum h) νN).restrict
        (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-d))) := by
  have hD := Langlands.AllField.RankinSelberg.TwoBlockLowerFourier.lowerDuality_measure_transport F h hN νN hνN
  exact ⟨(TwoBlockLowerFourier.lowerDuality F h).measurable,
    (hD.2.2 d).1⟩

variable (hMatrix : TwoBlockDominantDualMatrixStatement.{uF})

include hMatrix hN hνN

/-- Exact complex slice transport at complementary parameters, without any
convergence assumption or change of the supplied measure's scale. -/
theorem setIntegral_quotientKernel_reversedDual (s : ℂ) (d : ℤ) :
    (∫ q in Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-d),
      quotientKernel ν
        (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
        (reversedDualSectionEquiv F h σ hσ f) (reversedDualTest hr ψ Wtest)
        (by omega : r=t+(k+j+1)) (1-s) q
        ∂lowerMeasure F (reverse_sum h) νN) =
      ∫ q in Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h d,
        quotientKernel ν ell f Wtest hr s q ∂lowerMeasure F h νN := by
  have hD := lowerDuality_restrict_measurePreserving F h νN hN hνN d
  rw [← hD.integral_comp
    (TwoBlockLowerFourier.lowerDuality F h).toMeasurableEquiv.measurableEmbedding]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun q =>
    quotientKernel_reversedDual F h σ hσ ψ ell hr hMatrix f Wtest ν s q

/-- The actual zero-parameter complex coefficients reflect with the exact
residue-cardinality multiplier. This is a total-integral identity. -/
theorem reversedDualSliceCoefficient_eq (d : ℤ) :
    reversedDualSliceCoefficient F h σ hσ ψ ell hr f Wtest ν νN d =
      ((⟨⟩ : LocalFieldData F).residueCardinality : ℂ) ^ d *
        kernelSliceCoefficient ν ell f Wtest νN hr (-d) := by
  have heq := setIntegral_quotientKernel_reversedDual F h σ hσ ψ ell hr
    f Wtest ν νN hN hνN hMatrix 1 (-d)
  simp only [sub_self, neg_neg] at heq
  change (∫ q in Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) d,
    quotientKernel ν
      (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
      (reversedDualSectionEquiv F h σ hσ f) (reversedDualTest hr ψ Wtest)
      (by omega : r=t+(k+j+1)) 0 q ∂lowerMeasure F (reverse_sum h) νN) = _
  rw [heq, setIntegral_quotientKernel_spectral]
  simp only [spectralPoint, Complex.cpow_neg, Complex.cpow_one, inv_zpow,
    zpow_neg, inv_inv]
  exact mul_comm _ _

end Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
