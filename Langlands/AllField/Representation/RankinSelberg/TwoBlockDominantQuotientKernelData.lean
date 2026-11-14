import Langlands.Representation.RankinSelberg.TwoBlockDominantQuotientKernelData
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantOuterIntegralData
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantRawKernel
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantRectangleHaar
/-!
# Actual dominant rectangle integrals on the lower quotient

The simultaneous covariance of the raw kernel, followed by exact supplied-Haar
change of variables, gives complex, real norm-profile and Prop-valued descent.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg.TwoBlockDominantRectangular hiding AbsoluteInput FiberIntegrable KernelAbsoluteIntegrable KernelNormProfileIntegrable KernelOuterIntegrable NormProfileIntegrable OuterIntegrable absoluteInput_standard_iff ae_lowerQuotientMeasure_iff determinantWeight_lowerBlockUnipotent_mul fiberIntegrable_lowerBlockUnipotent_mul_iff integrable_lowerQuotientMeasure_iff integrable_rectangleChange_iff integral_rectangleChange kernel kernelAbsoluteIntegrable_iff kernelAbsoluteIntegrable_standard_iff kernel_covariance kernel_eq measurePreserving_rectangleChange outerFieldT2 outerFieldTopology outerFieldValuation outerGeneralLinearGroup outerGeneralLinearLocallyCompact outerGeneralLinearSecondCountable outerLocalField quotientFiberIntegrable quotientKernel quotientKernelMeasurable quotientKernelTopology quotientKernel_mk quotientNormProfile quotientNormProfile_mk rawKernel rawKernel_covariance rawScalarValue rectangleChangeHomeomorph rectangleHaarBorel rectangleHaarLocalField rectangleHaarMeasurable rectangleHaarSecondCountable rectangleHaarTopology rectangleHaarValuation rectangleMatrixBorel rectangleMatrixSecondCountable rectangleMeasure rectangleMeasure_sigmaFinite rectanglesBorel representativeKernel representativeKernel_lowerBlockUnipotent_mul representativeNormProfile representativeNormProfile_lowerBlockUnipotent_mul standardCompatible standardCompatible_sigmaFinite
open Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.Whittaker hiding TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mul_upperUnipotent_mem_twoBlockCell swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerUnfolding hiding groupIntegrand groupIntegrand_def groupIntegrand_lowerBlockUnipotent_mul integrand integrand_mk integrand_mk_eq_groupIntegrand isTopologicalRing_carrier partialSection partialSection_apply partialSection_lowerBlockUnipotent_mul rowMeasure_map_vecMul_upperUnipotent scalarSection_lowerBlockUnipotent_mul sigmaFinite_additiveHaarMeasure whittaker_blockRotation_lowerBlockUnipotent_mul
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding
open Langlands.QuotientIntegration

universe uF uW

variable {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance quotientKernelMeasurable : MeasurableSpace F := borel _

variable {t r j k : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}
variable {ψ : UnitaryAdditiveCharacter F}
variable (ν : AdditiveHaarMeasure F)
variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
variable (f : Sections F h σ)
variable (Wtest : WhittakerFunctions ψ r)

/-- Total integral of the actual weighted raw kernel over both supplied-Haar rectangles. -/
def representativeKernel (hr : r = t + (j + k + 1)) (s : ℂ)
    (g : GeneralLinear (t + 1) F) : ℂ :=
  ∫ z : Rectangles m j k F,
    kernel ell f Wtest hr s g z.1 z.2 ∂rectangleMeasure F m j k ν

/-- The rectangle integral, rather than the fixed-rectangle kernel, is left invariant. -/
theorem representativeKernel_lowerBlockUnipotent_mul
    (hr : r = t + (j + k + 1)) (s : ℂ)
    (u : lowerBlockUnipotent h F) (g : GeneralLinear (t + 1) F) :
    representativeKernel ν ell f Wtest hr s (u.val * g) =
      representativeKernel ν ell f Wtest hr s g := by
  unfold representativeKernel
  calc
    _ = ∫ z : Rectangles m j k F,
        kernel ell f Wtest hr s g (rectangleChange h j k u z).1
          (rectangleChange h j k u z).2 ∂rectangleMeasure F m j k ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z =>
        kernel_covariance ell f Wtest hr s u g z.1 z.2
    _ = _ := integral_rectangleChange F h j k ν u
      (fun z => kernel ell f Wtest hr s g z.1 z.2)

/-- The actual complex quotient kernel, without choosing coset representatives. -/
def quotientKernel (hr : r = t + (j + k + 1)) (s : ℂ) :
    LowerQuotient h F → ℂ :=
  descend (lowerBlockUnipotent h F)
    (representativeKernel ν ell f Wtest hr s)
    (representativeKernel_lowerBlockUnipotent_mul ν ell f Wtest hr s)

/-- Exact representative formula, valid also for nonintegrable inputs under the
total Bochner convention. -/
@[simp] theorem quotientKernel_mk (hr : r = t + (j + k + 1)) (s : ℂ)
    (g : GeneralLinear (t + 1) F) :
    quotientKernel ν ell f Wtest hr s (Quotient.mk _ g) =
      ∫ z : Rectangles m j k F,
        kernel ell f Wtest hr s g z.1 z.2 ∂rectangleMeasure F m j k ν := rfl

/-- Integral of the norm of the raw kernel, retained as a total real integral. -/
def representativeNormProfile (hr : r = t + (j + k + 1)) (s : ℂ)
    (g : GeneralLinear (t + 1) F) : ℝ :=
  ∫ z : Rectangles m j k F,
    ‖kernel ell f Wtest hr s g z.1 z.2‖ ∂rectangleMeasure F m j k ν

theorem representativeNormProfile_lowerBlockUnipotent_mul
    (hr : r = t + (j + k + 1)) (s : ℂ)
    (u : lowerBlockUnipotent h F) (g : GeneralLinear (t + 1) F) :
    representativeNormProfile ν ell f Wtest hr s (u.val * g) =
      representativeNormProfile ν ell f Wtest hr s g := by
  unfold representativeNormProfile
  calc
    _ = ∫ z : Rectangles m j k F,
        ‖kernel ell f Wtest hr s g (rectangleChange h j k u z).1
          (rectangleChange h j k u z).2‖ ∂rectangleMeasure F m j k ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z =>
        congrArg norm (kernel_covariance ell f Wtest hr s u g z.1 z.2)
    _ = _ := integral_rectangleChange F h j k ν u
      (fun z => ‖kernel ell f Wtest hr s g z.1 z.2‖)

/-- The real norm profile on the actual quotient. This is not the norm of
`quotientKernel`. -/
def quotientNormProfile (hr : r = t + (j + k + 1)) (s : ℂ) :
    LowerQuotient h F → ℝ :=
  descend (lowerBlockUnipotent h F)
    (representativeNormProfile ν ell f Wtest hr s)
    (representativeNormProfile_lowerBlockUnipotent_mul ν ell f Wtest hr s)

@[simp] theorem quotientNormProfile_mk (hr : r = t + (j + k + 1)) (s : ℂ)
    (g : GeneralLinear (t + 1) F) :
    quotientNormProfile ν ell f Wtest hr s (Quotient.mk _ g) =
      ∫ z : Rectangles m j k F,
        ‖kernel ell f Wtest hr s g z.1 z.2‖ ∂rectangleMeasure F m j k ν := rfl

/-- Actual integrability of the rectangle fiber. No convergence is asserted. -/
def FiberIntegrable (hr : r = t + (j + k + 1)) (s : ℂ)
    (g : GeneralLinear (t + 1) F) : Prop :=
  Integrable (fun z : Rectangles m j k F => kernel ell f Wtest hr s g z.1 z.2)
    (rectangleMeasure F m j k ν)

/-- Actual fiber integrability is invariant in both directions under left translation. -/
theorem fiberIntegrable_lowerBlockUnipotent_mul_iff
    (hr : r = t + (j + k + 1)) (s : ℂ)
    (u : lowerBlockUnipotent h F) (g : GeneralLinear (t + 1) F) :
    FiberIntegrable ν ell f Wtest hr s (u.val * g) ↔
      FiberIntegrable ν ell f Wtest hr s g := by
  unfold FiberIntegrable
  have heq : (fun z : Rectangles m j k F =>
      kernel ell f Wtest hr s (u.val * g) z.1 z.2) =
      fun z => kernel ell f Wtest hr s g
        (rectangleChange h j k u z).1 (rectangleChange h j k u z).2 := by
    funext z
    exact kernel_covariance ell f Wtest hr s u g z.1 z.2
  rw [heq]
  exact integrable_rectangleChange_iff F h j k ν u
    (fun z => kernel ell f Wtest hr s g z.1 z.2)

/-- Prop-valued descent of actual fiber integrability, with no representative choice. -/
def quotientFiberIntegrable (hr : r = t + (j + k + 1)) (s : ℂ) :
    LowerQuotient h F → Prop :=
  descend (lowerBlockUnipotent h F)
    (FiberIntegrable ν ell f Wtest hr s)
    (fun u g => propext (fiberIntegrable_lowerBlockUnipotent_mul_iff
      ν ell f Wtest hr s u g))

section Outer

variable [MeasurableSpace (LeftUnipotentQuotient t F)]
  [BorelSpace (LeftUnipotentQuotient t F)]
variable [MeasurableSpace (LowerQuotient h F)]
  [BorelSpace (LowerQuotient h F)]

/-- Actual outer integrability of the complex quotient kernel. -/
def KernelOuterIntegrable (hr : r = t + (j + k + 1)) (s : ℂ)
    (νN : Measure (LeftUnipotentQuotient t F)) : Prop :=
  OuterIntegrable F h νN (quotientKernel ν ell f Wtest hr s)

/-- Actual outer integrability of the integral of the raw kernel's norm. -/
def KernelNormProfileIntegrable (hr : r = t + (j + k + 1)) (s : ℂ)
    (νN : Measure (LeftUnipotentQuotient t F)) : Prop :=
  NormProfileIntegrable F h νN (quotientNormProfile ν ell f Wtest hr s)

/-- Explicit absolute-input conditions for a prospective analytic successor.
Fiber integrability remains a separate almost-everywhere requirement. -/
def KernelAbsoluteIntegrable (hr : r = t + (j + k + 1)) (s : ℂ)
    (νN : Measure (LeftUnipotentQuotient t F)) : Prop :=
  AbsoluteInput F h νN (quotientKernel ν ell f Wtest hr s)
    (quotientNormProfile ν ell f Wtest hr s)
    (quotientFiberIntegrable ν ell f Wtest hr s)

omit [BorelSpace (LeftUnipotentQuotient t F)]
  [BorelSpace (LowerQuotient h F)] in
/-- All three actual convergence conditions, stated separately and not asserted. -/
theorem kernelAbsoluteIntegrable_iff (hr : r = t + (j + k + 1)) (s : ℂ)
    (νN : Measure (LeftUnipotentQuotient t F)) :
    KernelAbsoluteIntegrable ν ell f Wtest hr s νN ↔
      KernelOuterIntegrable ν ell f Wtest hr s νN ∧
      KernelNormProfileIntegrable ν ell f Wtest hr s νN ∧
      ∀ᵐ q ∂Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice.lowerMeasure F h νN,
        quotientFiberIntegrable ν ell f Wtest hr s q := Iff.rfl

/-- The full absolute-input predicate in standard quotient coordinates. -/
theorem kernelAbsoluteIntegrable_standard_iff
    (hr : r = t + (j + k + 1)) (s : ℂ)
    (νN : Measure (LeftUnipotentQuotient t F)) :
    KernelAbsoluteIntegrable ν ell f Wtest hr s νN ↔
      Integrable (fun q => quotientKernel ν ell f Wtest hr s
        ((lowerToStandard h F).symm q)) νN ∧
      Integrable (fun q => quotientNormProfile ν ell f Wtest hr s
        ((lowerToStandard h F).symm q)) νN ∧
      ∀ᵐ q ∂νN, quotientFiberIntegrable ν ell f Wtest hr s
        ((lowerToStandard h F).symm q) :=
  absoluteInput_standard_iff F h νN (quotientKernel ν ell f Wtest hr s)
    (quotientNormProfile ν ell f Wtest hr s)
    (quotientFiberIntegrable ν ell f Wtest hr s)

end Outer

end Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
