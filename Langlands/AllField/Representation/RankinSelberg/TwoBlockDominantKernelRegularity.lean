import Langlands.Representation.RankinSelberg.TwoBlockDominantKernelRegularity
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankModelConvergenceProof
import Langlands.AllField.Representation.RankinSelberg.QuotientIwasawaIntegrationProof
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantQuotientKernelData
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerIntegrandRegularity
/-!
# Regularity of the actual dominant rectangle kernel

The raw weighted kernel is continuous for smooth coefficient-image tests.
Its total rectangle averages and the set of integrable rectangle fibers are
measurable, both on representatives and on the lower quotient.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg.TwoBlockDominantRectangular hiding AbsoluteInput FiberIntegrable KernelAbsoluteIntegrable KernelNormProfileIntegrable KernelOuterIntegrable NormProfileIntegrable OuterIntegrable absoluteInput_standard_iff ae_lowerQuotientMeasure_iff continuous_kernel determinantWeight_lowerBlockUnipotent_mul fiberIntegrable_lowerBlockUnipotent_mul_iff integrable_lowerQuotientMeasure_iff integrable_rectangleChange_iff integral_rectangleChange kernel kernelAbsoluteIntegrable_iff kernelAbsoluteIntegrable_standard_iff kernelRegularityBorel kernelRegularityGLBorel kernelRegularityGLLocallyCompact kernelRegularityGLMeasurable kernelRegularityGLSecondCountable kernelRegularityLocalField kernelRegularityMatrixBorel kernelRegularityMatrixSecondCountable kernelRegularityMeasurable kernelRegularitySecondCountable kernelRegularityT2 kernelRegularityTopology kernelRegularityValuation kernel_covariance kernel_eq measurable_quotientKernel measurable_quotientNormProfile measurable_representativeKernel measurable_representativeNormProfile measurePreserving_rectangleChange outerFieldT2 outerFieldTopology outerFieldValuation outerGeneralLinearGroup outerGeneralLinearLocallyCompact outerGeneralLinearSecondCountable outerLocalField quotientFiberIntegrable quotientKernel quotientKernelMeasurable quotientKernelTopology quotientKernel_mk quotientNormProfile quotientNormProfile_mk rawKernel rawKernel_covariance rawScalarValue rectangleChangeHomeomorph rectangleHaarBorel rectangleHaarLocalField rectangleHaarMeasurable rectangleHaarSecondCountable rectangleHaarTopology rectangleHaarValuation rectangleMatrixBorel rectangleMatrixSecondCountable rectangleMeasure rectangleMeasure_sigmaFinite rectanglesBorel representativeKernel representativeKernel_lowerBlockUnipotent_mul representativeNormProfile representativeNormProfile_lowerBlockUnipotent_mul standardCompatible standardCompatible_sigmaFinite
open Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice quotientIwasawaIntegration rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.Whittaker hiding TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement padicMatrixFourierSlice padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerUnfolding hiding coefficient_locallyConstant groupIntegrand groupIntegrand_def groupIntegrand_locallyConstant groupIntegrand_lowerBlockUnipotent_mul integrand integrand_continuous integrand_locallyConstant integrand_measurable integrand_mk integrand_mk_eq_groupIntegrand isTopologicalRing_carrier partialSection partialSection_apply partialSection_locallyConstant partialSection_lowerBlockUnipotent_mul rowMeasure_map_vecMul_upperUnipotent scalarSection_locallyConstant scalarSection_lowerBlockUnipotent_mul sectionEval_locallyConstant sigmaFinite_additiveHaarMeasure whittaker_blockRotation_lowerBlockUnipotent_mul
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding
open Langlands.QuotientIntegration

universe uF uV uW

section Matrices


end Matrices

variable {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance kernelRegularityT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance kernelRegularitySecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance kernelRegularityMeasurable : MeasurableSpace F := borel _
local instance kernelRegularityBorel : BorelSpace F := ⟨rfl⟩
local instance kernelRegularityMatrixBorel (a b : ℕ) :
    BorelSpace (Matrix (Fin a) (Fin b) F) :=
  inferInstanceAs (BorelSpace (Fin a → Fin b → F))
local instance kernelRegularityMatrixSecondCountable (a b : ℕ) :
    SecondCountableTopology (Matrix (Fin a) (Fin b) F) :=
  inferInstanceAs (SecondCountableTopology (Fin a → Fin b → F))
local instance kernelRegularityGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear n F) := borel _
local instance kernelRegularityGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear n F) := ⟨rfl⟩
local instance kernelRegularityGLSecondCountable (n : ℕ) :
    SecondCountableTopology (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology n
local instance kernelRegularityGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace n

variable {t r j k : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}
variable {ψ : UnitaryAdditiveCharacter F}
variable (ν : AdditiveHaarMeasure F)
variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
variable (f : Sections F h σ)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (GeneralLinear (r + 1) F) V)
variable (hπ : IsSmooth π) (lambda : glFunctionals ψ r π)
variable (Wtest : (coefficientModel π lambda).toSubmodule)

include hπ

/-- Smoothness alone gives joint continuity of the actual weighted raw kernel,
with no absolute-integrability premise. -/
theorem continuous_kernel (hr : r = t + (j + k + 1)) (s : ℂ) :
    Continuous (fun z : GeneralLinear (t + 1) F × Rectangles m j k F =>
      kernel ell f Wtest.val hr s z.1 z.2.1 z.2.2) := by
  have hf := (scalarSection_locallyConstant (fun i => (ell i).val) f 1).continuous
  have hW := (coefficient_locallyConstant π hπ lambda Wtest).continuous
  exact ((hf.comp continuous_fst).mul (hW.comp (continuous_matrix h hr))).mul
    ((continuous_adjacentRank_determinantWeight F (t + 1)
      (s - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ))).comp continuous_fst)

/-- The complex total rectangle integral is measurable even when some fibers
are not integrable. -/
theorem measurable_representativeKernel (hr : r = t + (j + k + 1)) (s : ℂ) :
    Measurable (representativeKernel ν ell f Wtest.val hr s) :=
  (continuous_kernel ell f π hπ lambda Wtest hr s).measurable.stronglyMeasurable
    |>.integral_prod_right' |>.measurable

/-- Measurability concerns the integral of the raw norm, retaining the exact
supplied rectangle Haar measure. -/
theorem measurable_representativeNormProfile (hr : r = t + (j + k + 1)) (s : ℂ) :
    Measurable (representativeNormProfile ν ell f Wtest.val hr s) :=
  (continuous_kernel ell f π hπ lambda Wtest hr s).norm.measurable.stronglyMeasurable
    |>.integral_prod_right' |>.measurable

variable [MeasurableSpace (LowerQuotient h F)]
  [BorelSpace (LowerQuotient h F)]

/-- Measurability of the actual complex average descends without choosing
representatives. -/
theorem measurable_quotientKernel (hr : r = t + (j + k + 1)) (s : ℂ) :
    Measurable (quotientKernel ν ell f Wtest.val hr s) := by
  apply (measurable_quotient_iff _ (isClosed_lowerBlockUnipotent_canonical F h) _).2
  exact measurable_representativeKernel ν ell f π hπ lambda Wtest hr s

/-- The actual real raw-norm profile is measurable on the lower quotient. -/
theorem measurable_quotientNormProfile (hr : r = t + (j + k + 1)) (s : ℂ) :
    Measurable (quotientNormProfile ν ell f Wtest.val hr s) := by
  apply (measurable_quotient_iff _ (isClosed_lowerBlockUnipotent_canonical F h) _).2
  exact measurable_representativeNormProfile ν ell f π hπ lambda Wtest hr s

end Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
