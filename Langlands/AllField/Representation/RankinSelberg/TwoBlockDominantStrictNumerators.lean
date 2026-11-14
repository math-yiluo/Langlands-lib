import Langlands.Representation.RankinSelberg.TwoBlockDominantStrictNumerators
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantDualSlices
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantStrictCoefficients
/-!
# Finite numerators for actual strictly dominant Jacquet coefficients

Support and the actual lower Fourier coefficient law are discharged. The two
first-block Laurent identities remain explicit premises.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg.DominantRankTransport hiding coe_strictResidueCardinalityUnit strictCoefficientBorel strictCoefficientMeasurable strictCoefficientQuotientMeasurable strictCoefficientSecondCountable strictCoefficientTopology strictDualSliceCoefficient strictDualSliceCoefficient_lowerSupport strictNumeratorGLBorel strictNumeratorGLMeasurable strictNumeratorGLTopology strictNumeratorLocalField strictNumeratorLowerMeasurable strictNumeratorMeasurable strictNumeratorQuotientMeasurable strictNumeratorTopology strictNumeratorUnipotentBorel strictNumeratorUnipotentMeasurable strictNumeratorValuation strictRectangleMeasure strictResidueCardinalityUnit strictSliceCoefficient strictSliceCoefficient_lowerSupport twoBlock_strictInducedCoefficient_numerators unequalRankSliceCoefficient_lowerSupport
open Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement EqualRankAnalyticStatement EqualRankContinuedFormsStatement EqualRankFunctionalEquationStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt TwoBlockDualSectionJacquetStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankContinuedForms equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_schwartzBruhat_row_bound hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice setIntegral_unequalRankAverage_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrableAt_unequalRankAverage_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice twoBlockDualSectionJacquet unequalRankAverage unequalRankAverage_eq_mul_spectralPoint_zpow unequalRankIntegrand_eq_mul_spectralPoint_zpow unequalRankSliceCoefficient unequalRankSliceExpansion unequalRankSliceExpansion_of_converges unequalSliceMatrixMeasurable unequalSliceQuotientBorel unequalSliceQuotientMeasurable unequalSliceTopology zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory LaurentPolynomial
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement padicMatrixFourierSlice padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockDominantRectangular hiding AbsoluteInput FiberIntegrable KernelAbsoluteIntegrable KernelNormProfileIntegrable KernelOuterIntegrable NormProfileIntegrable OuterIntegrable absoluteInput_standard_iff ae_lowerQuotientMeasure_iff ae_quotientFiberIntegrable_spectral_iff determinantWeight_lowerBlockUnipotent_mul dualKernelLocalField dualKernelMeasurable dualKernelTopology dualKernelValuation dualRectangleBorel dualRectangleLocalField dualRectangleMatrixBorel dualRectangleMatrixSecondCountable dualRectangleMeasurable dualRectangleProductBorel dualRectangleSecondCountable dualRectangleTopology dualRectangleValuation dualSlicesGLBorel dualSlicesGLMeasurable dualSlicesGLTopologicalGroup dualSlicesLocalField dualSlicesLowerBorel dualSlicesLowerMeasurable dualSlicesMeasurable dualSlicesStandardMeasurable dualSlicesTopology dualSlicesUnipotentBorel dualSlicesUnipotentMeasurable dualSlicesValuation fiberIntegrable_lowerBlockUnipotent_mul_iff fiberIntegrable_spectral_iff integrableOn_quotientKernel_spectral_iff integrableOn_quotientNormProfile_spectral_iff integrable_lowerQuotientMeasure_iff integrable_rectangleChange_iff integral_dualRectangleEquiv integral_rectangleChange kernel kernelAbsoluteIntegrable_iff kernelAbsoluteIntegrable_restrict_spectral_iff kernelAbsoluteIntegrable_standard_iff kernelSliceCoefficient kernel_covariance kernel_eq kernel_reversedDual kernel_spectral lowerDuality_restrict_measurePreserving measurePreserving_dualRectangleEquiv measurePreserving_rectangleChange outerFieldT2 outerFieldTopology outerFieldValuation outerGeneralLinearGroup outerGeneralLinearLocallyCompact outerGeneralLinearSecondCountable outerLocalField quotientFiberIntegrable quotientFiberIntegrable_spectral_iff quotientKernel quotientKernelMeasurable quotientKernelTopology quotientKernel_mk quotientKernel_reversedDual quotientKernel_spectral quotientKernel_spectral_onSlice quotientNormProfile quotientNormProfile_mk quotientNormProfile_spectral quotientNormProfile_spectral_onSlice rawKernel rawKernel_covariance rawKernel_reversedDual rawScalarValue rectangleChangeHomeomorph rectangleHaarBorel rectangleHaarLocalField rectangleHaarMeasurable rectangleHaarSecondCountable rectangleHaarTopology rectangleHaarValuation rectangleMatrixBorel rectangleMatrixSecondCountable rectangleMeasure rectangleMeasure_sigmaFinite rectanglesBorel representativeKernel representativeKernel_lowerBlockUnipotent_mul representativeKernel_reversedDual representativeKernel_spectral representativeNormProfile representativeNormProfile_lowerBlockUnipotent_mul representativeNormProfile_spectral reversedDualSectionEquiv reversedDualSectionEquiv_scalar reversedDualSliceCoefficient reversedDualSliceCoefficient_eq setIntegral_quotientKernel_reversedDual setIntegral_quotientKernel_spectral sliceSpectralMeasurable sliceSpectralTopology standardCompatible standardCompatible_sigmaFinite
open Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.HarmonicAnalysis.BilateralLaurentSeries

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance strictNumeratorMeasurable : MeasurableSpace F := borel _
local instance strictNumeratorQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F) := borel _

section Support

variable {n r j k : ℕ}

/-- Actual dual coefficient, with the source's right Weyl translation and
exchanged complementary rectangle sizes. -/
def strictDualSliceCoefficient (hr : r = n + (j + k + 1))
    (ψ : UnitaryAdditiveCharacter F)
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : AdditiveHaarMeasure F)
    (Wtest : WhittakerFunctions ψ r)
    (WjacD : InverseWhittakerFunctions (ψ.scale (-1)) n) :
    BilateralLaurentSeries :=
  strictSliceCoefficient F (by omega : r = n + (k + j + 1))
    (ψ.scale (-1)) μ ν (reversedDualTest hr ψ Wtest) WjacD

/-- The prescribed translated dual test lies in the actual smooth
inverse-transpose model, so its coefficients also have a finite negative tail. -/
theorem strictDualSliceCoefficient_lowerSupport
    (hr : r = n + (j + k + 1))
    (ψ : UnitaryAdditiveCharacter F)
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : AdditiveHaarMeasure F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hπ : IsSmooth π) (lambda : glFunctionals ψ r π)
    (f : (coefficientModel π lambda).toSubmodule)
    (WjacD : InverseWhittakerFunctions (ψ.scale (-1)) n) :
    HasLowerBoundedSupport
      (strictDualSliceCoefficient F hr ψ μ ν f.val WjacD) := by
  exact strictSliceCoefficient_lowerSupport F (by omega : r = n + (k + j + 1))
    (ψ.scale (-1)) μ ν (inverseTransposePullback π)
    (Whittaker.inverseTransposePullback_isSmooth π hπ)
    (firstDualFunctional ψ π lambda)
    (translatedFirstDualModelEquiv ψ π lambda (rightWeyl hr) f) WjacD

end Support

/-- The canonical nonzero residue cardinality, as a complex unit. -/
def strictResidueCardinalityUnit : ℂˣ :=
  Units.mk0 ((⟨⟩ : LocalFieldData F).residueCardinality : ℂ) (by
    have hq : (⟨⟩ : LocalFieldData F).residueCardinality ≠ 0 :=
      ne_of_gt (lt_trans Nat.zero_lt_one
        (⟨⟩ : LocalFieldData F).residueCardinality_gt_one)
    exact_mod_cast hq)

@[simp]
theorem coe_strictResidueCardinalityUnit :
    (strictResidueCardinalityUnit F : ℂ) =
      ((⟨⟩ : LocalFieldData F).residueCardinality : ℂ) := rfl

section Induced

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
  [hmod : ∀ i, Module ℂ (W i)]

local instance strictNumeratorGLTopology :
    IsTopologicalGroup (GeneralLinear (t + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
local instance strictNumeratorGLMeasurable :
    MeasurableSpace (GeneralLinear (t + 1) F) := borel _
local instance strictNumeratorGLBorel :
    BorelSpace (GeneralLinear (t + 1) F) := ⟨rfl⟩
local instance strictNumeratorUnipotentMeasurable :
    MeasurableSpace (upperUnipotent (t + 1) F) := borel _
local instance strictNumeratorUnipotentBorel :
    BorelSpace (upperUnipotent (t + 1) F) := ⟨rfl⟩
local instance strictNumeratorLowerMeasurable :
    MeasurableSpace (TwoBlockLowerUnipotentQuotient.LowerQuotient h F) :=
  borel _

variable (ψ : UnitaryAdditiveCharacter F)
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
  (hσ : ∀ i, IsSmooth (σ i))
  (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
  {r j k : ℕ} (hr : r = t + (j + k + 1))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (r + 1) F) V)
  (hπ : IsSmooth π) (lambda : glFunctionals ψ r π)
  (J : glInverseFunctionals ψ t (inducedRep F h σ))
  (JD : glInverseFunctionals (ψ.scale (-1)) t
    (inducedRep F (TwoBlockLowerUnipotentQuotient.reverse_sum h)
      (fun i => inverseTransposePullback (σ i.rev))))
  (μ : Measure (LeftUnipotentQuotient t F))
  (ν : AdditiveHaarMeasure F)
  (hN : Measure.IsMulRightInvariant (unipotentHaar F t))
  (hμ : IsCompatible (upperUnipotent (t + 1) F)
    (generalLinearHaar F t) (unipotentHaar F t) μ)
  (f : Sections F h σ) (Wtest : (coefficientModel π lambda).toSubmodule)

include hπ hN hμ

/-- The actual original and reversed-dual induced coefficients have a unique
finite numerator, conditional only on the two displayed first-block equations.
The support bounds, residue scalar and actual Fourier law are derived. -/
theorem twoBlock_strictInducedCoefficient_numerators
    (c₁ : ℂˣ) (d₁ : ℤ) (c₂ : ℂˣ) (d₂ : ℤ)
    (P₁ P₁D P₂ P₂D : Polynomial ℂ) :
    let q := strictResidueCardinalityUnit F
    let a := strictSliceCoefficient F hr ψ μ ν Wtest.val
      (modelMap (inducedRep F h σ) J f).val
    let aD := strictDualSliceCoefficient F hr ψ μ ν Wtest.val
      (modelMap
        (inducedRep F (TwoBlockLowerUnipotentQuotient.reverse_sum h)
          (fun i => inverseTransposePullback (σ i.rev))) JD
        (reversedDualSectionEquiv F h σ hσ f)).val
    let b : BilateralLaurentSeries :=
      kernelSliceCoefficient ν ell f Wtest.val μ hr
    let bD : BilateralLaurentSeries :=
      reversedDualSliceCoefficient F h σ hσ ψ ell hr f Wtest.val ν μ
    Polynomial.eval₂ C (C ((q : ℂ)⁻¹) * T (-1)) P₁D • b =
        (C (c₁ : ℂ) * T d₁ * P₁.toLaurent) • a →
    Polynomial.eval₂ C (C ((q : ℂ)⁻¹) * T (-1)) P₂ • bD =
        (C (c₂ : ℂ) * T d₂ * P₂D.toLaurent) • aD →
    ∃! R : LaurentPolynomial ℂ,
      ofLaurentPolynomial R = (P₁ * P₂).toLaurent • a ∧
      ofLaurentPolynomial (laurentReflection q R) =
        (laurentReflection q
          (↑(clearedProductMultiplierUnit q c₁ d₁ c₂ d₂)⁻¹ : LaurentPolynomial ℂ) *
            (P₁D * P₂D).toLaurent) • aD := by
  intro q a aD b bD hFirst hSecond
  have ha : HasLowerBoundedSupport a :=
    strictSliceCoefficient_lowerSupport F hr ψ μ ν π hπ lambda Wtest
      (modelMap (inducedRep F h σ) J f).val
  have haD : HasLowerBoundedSupport aD :=
    strictDualSliceCoefficient_lowerSupport F hr ψ μ ν π hπ lambda Wtest
      (modelMap
        (inducedRep F (TwoBlockLowerUnipotentQuotient.reverse_sum h)
          (fun i => inverseTransposePullback (σ i.rev))) JD
        (reversedDualSectionEquiv F h σ hσ f)).val
  have hFourier (d : ℤ) : bD (-d) = (q : ℂ) ^ (-d) * b d := by
    dsimp only [bD, b, q]
    simpa only [coe_strictResidueCardinalityUnit, neg_neg] using
      reversedDualSliceCoefficient_eq F h σ hσ ψ ell hr f Wtest.val ν μ
        hN hμ twoBlockDominantDualMatrix (-d)
  exact twoBlock_cleared_numerators q c₁ d₁ c₂ d₂ ha haD hFirst hSecond hFourier

end Induced

end Langlands.AllField.RankinSelberg.DominantRankTransport
