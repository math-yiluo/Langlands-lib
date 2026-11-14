import Langlands.Representation.RankinSelberg.TwoBlockDominantDualKernel
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankModelConvergenceProof
import Langlands.AllField.Representation.RankinSelberg.EqualRankContinuedFormsProofSupplement
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantDualRectangles
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantQuotientKernelData
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDualSectionJacquetProof
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFourierGeometry
import Langlands.AllField.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement
/-!
# Actual dominant kernels under reversed duality

The matrix comparison is an explicit premise. The section equivalence and
rectangle measures are the published actual constructions.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg.TwoBlockDominantRectangular hiding AbsoluteInput FiberIntegrable KernelAbsoluteIntegrable KernelNormProfileIntegrable KernelOuterIntegrable NormProfileIntegrable OuterIntegrable absoluteInput_standard_iff ae_lowerQuotientMeasure_iff determinantWeight_lowerBlockUnipotent_mul dualKernelLocalField dualKernelMeasurable dualKernelTopology dualKernelValuation dualRectangleBorel dualRectangleLocalField dualRectangleMatrixBorel dualRectangleMatrixSecondCountable dualRectangleMeasurable dualRectangleProductBorel dualRectangleSecondCountable dualRectangleTopology dualRectangleValuation fiberIntegrable_lowerBlockUnipotent_mul_iff integrable_lowerQuotientMeasure_iff integrable_rectangleChange_iff integral_dualRectangleEquiv integral_rectangleChange kernel kernelAbsoluteIntegrable_iff kernelAbsoluteIntegrable_standard_iff kernel_covariance kernel_eq kernel_reversedDual measurePreserving_dualRectangleEquiv measurePreserving_rectangleChange outerFieldT2 outerFieldTopology outerFieldValuation outerGeneralLinearGroup outerGeneralLinearLocallyCompact outerGeneralLinearSecondCountable outerLocalField quotientFiberIntegrable quotientKernel quotientKernelMeasurable quotientKernelTopology quotientKernel_mk quotientKernel_reversedDual quotientNormProfile quotientNormProfile_mk rawKernel rawKernel_covariance rawKernel_reversedDual rawScalarValue rectangleChangeHomeomorph rectangleHaarBorel rectangleHaarLocalField rectangleHaarMeasurable rectangleHaarSecondCountable rectangleHaarTopology rectangleHaarValuation rectangleMatrixBorel rectangleMatrixSecondCountable rectangleMeasure rectangleMeasure_sigmaFinite rectanglesBorel representativeKernel representativeKernel_lowerBlockUnipotent_mul representativeKernel_reversedDual representativeNormProfile representativeNormProfile_lowerBlockUnipotent_mul reversedDualSectionEquiv reversedDualSectionEquiv_scalar standardCompatible standardCompatible_sigmaFinite
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

universe uF uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i+1) = t+1)
  {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
  [hmod : ∀ i, Module ℂ (W i)]
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i+1) F) (W i))

local instance dualKernelMeasurable : MeasurableSpace F := borel F

variable (hσ : ∀ i, IsSmooth (σ i))

/-- An actual reversed-dual section equivalence chosen from the published
Jacquet transport before all characters, functionals, tests and measures. -/
def reversedDualSectionEquiv :
    Representation.Equiv
      (inverseTransposePullback (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ))
      (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F (reverse_sum h)
        (fun i => inverseTransposePullback (σ i.rev))) :=
  Classical.choose (twoBlockDualSectionJacquet F t m h W σ hσ)

variable (ψ : UnitaryAdditiveCharacter F)
  (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))

/-- Scalar realization for this fixed actual equivalence. -/
theorem reversedDualSectionEquiv_scalar
    (f : Sections F h σ) (g : GeneralLinear (t+1) F) :
    scalarSection (fun i => (secondDualFunctional ψ (σ i.rev) (ell i.rev)).val)
        (reversedDualSectionEquiv F h σ hσ f) g 1 =
      scalarSection (fun i => (ell i).val) f
        (weylLong (t+1) F * inverseTranspose (t+1) F g) 1 := by
  have hE := Classical.choose_spec (twoBlockDualSectionJacquet F t m h W σ hσ)
  exact (hE.2.2 ψ ell).2.1 f g

variable {r j k : ℕ} (hr : r=t+(j+k+1))
  (hMatrix : TwoBlockDominantDualMatrixStatement.{uF})
  (f : Sections F h σ) (Wtest : WhittakerFunctions ψ r)

include hMatrix in
/-- The actual unweighted kernels agree after signed exchange, with the
prescribed right Weyl translation in the first dual test. -/
theorem rawKernel_reversedDual
    (g : GeneralLinear (t+1) F)
    (z : Rectangles (fun i => m i.rev) k j F) :
    rawKernel (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
        (reversedDualSectionEquiv F h σ hσ f) (reversedDualTest hr ψ Wtest)
        (by omega : r=t+(k+j+1))
        (weylLong (t+1) F * inverseTranspose (t+1) F g) z.1 z.2 =
      rawKernel ell f Wtest hr g
        (dualRectangleEquiv m j k z).1 (dualRectangleEquiv m j k z).2 := by
  have hM := ((hMatrix F t r j k m h hr).2 z.1 z.2).2 g
  unfold rawKernel rawScalarValue
  rw [reversedDualSectionEquiv_scalar]
  have hinv :
      weylLong (t+1) F * inverseTranspose (t+1) F
        (weylLong (t+1) F * inverseTranspose (t+1) F g) = g := by
    simpa only [weylInverseTranspose_apply] using
      weylInverseTranspose_involutive (t+1) F g
  rw [hinv, reversedDualTest_apply]
  change _ * Wtest.val
      (weylLong (r+1) F *
        inverseTranspose (r+1) F (reversedMatrix h hr
          (weylLong (t+1) F * inverseTranspose (t+1) F g) z.1 z.2)) = _
  rw [hM]
  rfl

include hMatrix in
/-- The actual weighted kernels agree at the complementary complex parameters. -/
theorem kernel_reversedDual (s : ℂ)
    (g : GeneralLinear (t+1) F)
    (z : Rectangles (fun i => m i.rev) k j F) :
    kernel (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
        (reversedDualSectionEquiv F h σ hσ f) (reversedDualTest hr ψ Wtest)
        (by omega : r=t+(k+j+1)) (1-s)
        (weylLong (t+1) F * inverseTranspose (t+1) F g) z.1 z.2 =
      kernel ell f Wtest hr s g
        (dualRectangleEquiv m j k z).1 (dualRectangleEquiv m j k z).2 := by
  unfold kernel
  rw [rawKernel_reversedDual F h σ hσ ψ ell hr hMatrix f Wtest,
    dualDeterminantWeight]

include hMatrix

variable (ν : AdditiveHaarMeasure F)

/-- Exact supplied-Haar change of variables for the complex rectangle integral.
This is an equality of total integrals and does not assert convergence. -/
theorem representativeKernel_reversedDual (s : ℂ)
    (g : GeneralLinear (t+1) F) :
    representativeKernel ν
        (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
        (reversedDualSectionEquiv F h σ hσ f) (reversedDualTest hr ψ Wtest)
        (by omega : r=t+(k+j+1)) (1-s)
        (weylLong (t+1) F * inverseTranspose (t+1) F g) =
      representativeKernel ν ell f Wtest hr s g := by
  unfold representativeKernel
  simp_rw [kernel_reversedDual F h σ hσ ψ ell hr hMatrix f Wtest]
  exact integral_dualRectangleEquiv F m j k ν
    (fun z => kernel ell f Wtest hr s g z.1 z.2)

/-- The complex identity descends along the actual published lower duality. -/
theorem quotientKernel_reversedDual (s : ℂ)
    (q : LowerQuotient h F) :
    quotientKernel ν
        (fun i => secondDualFunctional ψ (σ i.rev) (ell i.rev))
        (reversedDualSectionEquiv F h σ hσ f) (reversedDualTest hr ψ Wtest)
        (by omega : r=t+(k+j+1)) (1-s)
        (TwoBlockLowerFourier.lowerDuality F h q) =
      quotientKernel ν ell f Wtest hr s q := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [TwoBlockLowerFourier.lowerDuality_mk]
    exact representativeKernel_reversedDual F h σ hσ ψ ell hr hMatrix f Wtest ν s g

end Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
