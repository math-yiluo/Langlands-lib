import Langlands.Representation.RankinSelberg.TwoBlockDominantStrictFiniteNumerators
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantStrictSecondBlock
/-! # Actual finite numerators at strictly dominant rank -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg.DominantRankTransport hiding EqualFirstBlockCoefficientLaw EqualLowerFourierCoefficientLaw EqualTwoSidedFirstBlockLaws StrictFirstBlockCoefficientLaw StrictFirstBlockFactorCertificate StrictTwoBlockFiniteNumerators StrictTwoSidedFirstBlockLaws coe_strictResidueCardinalityUnit determinantComplexPower_inverseTranspose determinantComplexPower_weylLong dualJacquetLocalField dualJacquetTopology dualJacquetValuation equalDualityBorel equalDualityGLBorel equalDualityGLMeasurable equalDualityLocalField equalDualityLowerBorel equalDualityLowerMeasurable equalDualityMeasurable equalDualityQuotientMeasurable equalDualityTopology equalDualityUnipotentBorel equalDualityUnipotentMeasurable equalDualityValuation equalFirstBlockBorel equalFirstBlockGLBorel equalFirstBlockGLMeasurable equalFirstBlockLocalField equalFirstBlockLowerMeasurable equalFirstBlockLowerSeries equalFirstBlockMeasurable equalFirstBlockQuotientMeasurable equalFirstBlockSecondCountable equalFirstBlockTopology equalFirstBlockUnipotentBorel equalFirstBlockUnipotentMeasurable equalFirstBlockValuation equalLowerFourierCoefficientLaw equalLowerGroupIntegrand_reversedDual equalLowerIntegrand_reversedDual equalSecondBlockBorel equalSecondBlockGLBorel equalSecondBlockGLMeasurable equalSecondBlockLocalField equalSecondBlockMeasurable equalSecondBlockQuotientMeasurable equalSecondBlockSecondCountable equalSecondBlockTopology equalSecondBlockUnipotentBorel equalSecondBlockUnipotentMeasurable equalSecondBlockValuation exists_equalFirstBlockBound_forOrdinaryFunctional exists_equalFirstBlockCoefficientLaw exists_equalTwoSidedFirstBlockLaws exists_reversedEqualFirstBlockBound exists_reversedStrictFirstBlockBound exists_strictFirstBlockBound_forOrdinaryFunctional exists_strictFirstBlockCoefficientLaw exists_strictTwoBlockFiniteNumerators exists_strictTwoSidedFirstBlockLaws instBorelSpaceCarrier instMeasurableSpaceCarrier instTopologicalSpaceCarrier lowerInduced_inverseWhittakerType negatedSelfDualHaar negatedSelfDualHaar_val radicalAverage_eq_equalRankIntegrand reversedDualBlocks_whittakerType reversedDualSectionEquiv_ordinary reversedDual_oppositeTwistBlocks secondDual_oppositeTwistFunctional_val strictCoefficientBorel strictCoefficientMeasurable strictCoefficientQuotientMeasurable strictCoefficientSecondCountable strictCoefficientTopology strictDualSliceCoefficient strictDualSliceCoefficient_lowerSupport strictFiniteNumeratorGLBorel strictFiniteNumeratorGLMeasurable strictFiniteNumeratorLocalField strictFiniteNumeratorLowerMeasurable strictFiniteNumeratorQuotientMeasurable strictFiniteNumeratorTopology strictFiniteNumeratorUnipotentBorel strictFiniteNumeratorUnipotentMeasurable strictFiniteNumeratorValuation strictFirstBlockGLBorel strictFirstBlockGLMeasurable strictFirstBlockLocalField strictFirstBlockLowerMeasurable strictFirstBlockQuotientMeasurable strictFirstBlockTopology strictFirstBlockUnipotentBorel strictFirstBlockUnipotentMeasurable strictFirstBlockValuation strictNumeratorGLBorel strictNumeratorGLMeasurable strictNumeratorGLTopology strictNumeratorLocalField strictNumeratorLowerMeasurable strictNumeratorMeasurable strictNumeratorQuotientMeasurable strictNumeratorTopology strictNumeratorUnipotentBorel strictNumeratorUnipotentMeasurable strictNumeratorValuation strictRectangleMeasure strictResidueCardinalityUnit strictSecondBlockGLBorel strictSecondBlockGLMeasurable strictSecondBlockLocalField strictSecondBlockQuotientMeasurable strictSecondBlockTopology strictSecondBlockUnipotentBorel strictSecondBlockUnipotentMeasurable strictSecondBlockValuation strictSliceCoefficient strictSliceCoefficient_lowerSupport strictTwoBlockFiniteNumerators_of_laws twoBlock_strictInducedCoefficient_numerators unequalRankSliceCoefficient_lowerSupport unfoldedJacquetSeries unfoldedJacquetSeries_eq
open Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement EqualRankAnalyticStatement EqualRankContinuedFormsStatement EqualRankFrobeniusStatement EqualRankFunctionalEquationStatement EqualRankLastRowReductionStatement EqualRankNormalizedCompactIntegrationStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement EqualRankTrilinearUniquenessStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement LowerFirstBlockIntegrationInputStatement LowerFirstBlockSliceTowerInputStatement NormalizedProductWhittakerTypeStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement SliceIntegrable SliceIntegrableAt TwoBlockDominantFirstBlockLaurentIdentityStatement TwoBlockDualSectionJacquetStatement TwoBlockFirstBlockLaurentIdentityStatement TwoBlockFirstBlockQuotientIntegrationStatement TwoBlockFixedSliceUnfoldingStatement TwoBlockJacquetConvergenceStatement TwoBlockLowerFirstBlockQuotientIntegrationStatement TwoBlockLowerFixedSliceConvergenceStatement TwoBlockOrdinaryJacquetFunctionalStatement TwoBlockUnipotentQuotientIntegrationStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerRowSliceCompactSupportStatement ZeroRowLastRowCutoffStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankPure_hasCompactSupport assembleLowerFirstBlockQuotientIntegration continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankContinuedForms equalRankFrobenius equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankLastRowReduction equalRankNormalizedCompactIntegration equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_iwasawa_diagonal_le_of_simpleRoot exists_schwartzBruhat_row_bound finiteFunctionMellin finiteFunctionShellSeries hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lastRowCompactOrbit lowerFirstBlockIntegrationInput_of_sliceTower lowerFirstBlockSliceTowerInput measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow normalizedProductWhittakerType oneVariableMellin padicPairGammaConstructionInput_iff padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType padic_quotient_sigmaFinite padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice quotientIwasawaIntegration quotientRootIntegration rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight setIntegral_equalRankIntegrand_determinantSlice setIntegral_unequalRankAverage_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrableAt_unequalRankAverage_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockDualSectionJacquet twoBlockFirstBlockLaurentIdentity twoBlockFirstBlockQuotientIntegration twoBlockFixedSliceUnfolding twoBlockJacquetConvergence twoBlockLowerFirstBlockQuotientIntegration twoBlockLowerFixedSliceConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val twoBlockOrdinaryJacquetFunctional twoBlockUnipotentQuotientIntegration unequalRankAnalytic unequalRankAverage unequalRankAverage_eq_mul_spectralPoint_zpow unequalRankCommonGenerator unequalRankCompactSupport unequalRankFiniteExpansion unequalRankFunctionalEquation unequalRankGammaPropagation unequalRankIntegrand_eq_mul_spectralPoint_zpow unequalRankIwasawaSupport unequalRankSliceCoefficient unequalRankSliceExpansion unequalRankSliceExpansion_of_converges unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unequalSliceMatrixMeasurable unequalSliceQuotientBorel unequalSliceQuotientMeasurable unequalSliceTopology whittakerRowSliceCompactSupport zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory LaurentPolynomial
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement TwoBlockRowFourierCompanionStatement exists_rowSchwartz_order_lower_bound padicLatticeGeometry padicMatrixFourierSlice padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists padicUnipotentHaar_iota_fourier_duality_right twoBlockRowFourierCompanion
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding CompactLocalizationStatement MirabolicCompactTwistedPairingStatement MirabolicFiniteLengthStatement MirabolicFunctionalMultiplicityStatement MirabolicTwistedPairingRigidityStatement MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier UnipotentOrbitStatement compactLocalization exchangedParabolic functionalsCongr hasCompactSupport_twoBlockCellRestriction inducedLocalization_of_prerequisites mirabolicCompactTwistedPairing mirabolicFiniteLength mirabolicFunctionalMultiplicity mirabolicUnitTest modelKirillovTransfer mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentOrbit unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding blockRotation_inv_mem_integralOpen blockRotation_inv_mul_mem_integralOpen blockRotation_mem_integralOpen canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockDominantRectangular hiding AbsoluteInput FiberIntegrable KernelAbsoluteIntegrable KernelNormProfileIntegrable KernelOuterIntegrable NormProfileIntegrable OuterIntegrable absoluteInput_standard_iff ae_lowerQuotientMeasure_iff ae_quotientFiberIntegrable_spectral_iff determinantWeight_lowerBlockUnipotent_mul dualKernelLocalField dualKernelMeasurable dualKernelTopology dualKernelValuation dualRectangleBorel dualRectangleLocalField dualRectangleMatrixBorel dualRectangleMatrixSecondCountable dualRectangleMeasurable dualRectangleProductBorel dualRectangleSecondCountable dualRectangleTopology dualRectangleValuation dualSlicesGLBorel dualSlicesGLMeasurable dualSlicesGLTopologicalGroup dualSlicesLocalField dualSlicesLowerBorel dualSlicesLowerMeasurable dualSlicesMeasurable dualSlicesStandardMeasurable dualSlicesTopology dualSlicesUnipotentBorel dualSlicesUnipotentMeasurable dualSlicesValuation fiberIntegrable_lowerBlockUnipotent_mul_iff fiberIntegrable_spectral_iff integrableOn_quotientKernel_spectral_iff integrableOn_quotientNormProfile_spectral_iff integrable_lowerQuotientMeasure_iff integrable_rectangleChange_iff integral_dualRectangleEquiv integral_rectangleChange kernel kernelAbsoluteIntegrable_iff kernelAbsoluteIntegrable_restrict_spectral_iff kernelAbsoluteIntegrable_standard_iff kernelSliceCoefficient kernel_covariance kernel_eq kernel_reversedDual kernel_spectral lowerDuality_restrict_measurePreserving measurePreserving_dualRectangleEquiv measurePreserving_rectangleChange outerFieldT2 outerFieldTopology outerFieldValuation outerGeneralLinearGroup outerGeneralLinearLocallyCompact outerGeneralLinearSecondCountable outerLocalField quotientFiberIntegrable quotientFiberIntegrable_spectral_iff quotientKernel quotientKernelMeasurable quotientKernelTopology quotientKernel_mk quotientKernel_reversedDual quotientKernel_spectral quotientKernel_spectral_onSlice quotientNormProfile quotientNormProfile_mk quotientNormProfile_spectral quotientNormProfile_spectral_onSlice rawKernel rawKernel_covariance rawKernel_reversedDual rawScalarValue rectangleChangeHomeomorph rectangleHaarBorel rectangleHaarLocalField rectangleHaarMeasurable rectangleHaarSecondCountable rectangleHaarTopology rectangleHaarValuation rectangleMatrixBorel rectangleMatrixSecondCountable rectangleMeasure rectangleMeasure_sigmaFinite rectanglesBorel representativeKernel representativeKernel_lowerBlockUnipotent_mul representativeKernel_reversedDual representativeKernel_spectral representativeNormProfile representativeNormProfile_lowerBlockUnipotent_mul representativeNormProfile_spectral reversedDualSectionEquiv reversedDualSectionEquiv_scalar reversedDualSliceCoefficient reversedDualSliceCoefficient_eq setIntegral_quotientKernel_reversedDual setIntegral_quotientKernel_spectral sliceSpectralMeasurable sliceSpectralTopology standardCompatible standardCompatible_sigmaFinite
open Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.HarmonicAnalysis.BilateralLaurentSeries

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance strictFiniteNumeratorT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance strictFiniteNumeratorSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance strictFiniteNumeratorMeasurable : MeasurableSpace F := borel _
local instance strictFiniteNumeratorBorel : BorelSpace F := ⟨rfl⟩
local instance strictFiniteNumeratorGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance strictFiniteNumeratorGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance strictFiniteNumeratorUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance strictFiniteNumeratorUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
local instance strictFiniteNumeratorQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F) := borel _
local instance strictFiniteNumeratorQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩

variable {t r : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
  [hmod : ∀ i, Module ℂ (W i)]

local instance strictFiniteNumeratorLowerMeasurable :
    MeasurableSpace (LowerQuotient h F) := borel _
local instance strictFiniteNumeratorLowerBorel :
    BorelSpace (LowerQuotient h F) := ⟨rfl⟩
local instance strictFiniteNumeratorLowerDualMeasurable :
    MeasurableSpace (LowerQuotient (reverse_sum h) F) := borel _
local instance strictFiniteNumeratorLowerDualBorel :
    BorelSpace (LowerQuotient (reverse_sum h) F) := ⟨rfl⟩

local notation "qF" => (Langlands.LocalFieldData.residueCardinality (⟨⟩ : LocalFieldData F))
local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

variable (htr : t < r) (ψ : UnitaryAdditiveCharacter F)
  (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (r + 1) F) V)
  (lambda : glFunctionals ψ r π)
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
  (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))

variable (hσ : ∀ i, IsSmooth (σ i))
  (J : glInverseFunctionals ψ t (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ))
  (μN : Measure (LeftUnipotentQuotient t F))
  (μA : Measure (LeftUnipotentQuotient (m 0) F))
  (μB : Measure (LeftUnipotentQuotient (m 1) F))

/-- Both full first-block certificates and one finite numerator for every
actual coefficient, uniformly over all complementary row pairs. -/
def StrictTwoBlockFiniteNumerators : Prop :=
  let E := reversedDualSectionEquiv F h σ hσ
  let σD := fun i : Fin 2 => inverseTransposePullback (σ i.rev)
  let ellD := fun i : Fin 2 => secondDualFunctional ψ (σ i.rev) (ell i.rev)
  let JD := transportedSecondDualFunctional ψ (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) E J
  let q := strictResidueCardinalityUnit F
  ∃ (ζ₁ c₁ ζ₂ c₂ : ℂˣ) (d₁ d₂ : ℤ) (P₁ P₁D P₂ P₂D : Polynomial ℂ),
    StrictFirstBlockFactorCertificate F h htr ψ ν π lambda σ ell μA ζ₁ c₁ d₁ P₁ P₁D ∧
    StrictFirstBlockFactorCertificate F (reverse_sum h) htr (ψ.scale (-1))
      (negatedSelfDualHaar F ψ ν) (inverseTransposePullback π)
      (firstDualFunctional ψ π lambda) σD ellD μB ζ₂ c₂ d₂ P₂D P₂ ∧
    ∀ (j k : ℕ) (hr : r = t + (j + k + 1))
      (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σ)
      (Wtest : (coefficientModel π lambda).toSubmodule),
      let a := strictSliceCoefficient F hr ψ μN ν.val Wtest.val
        (modelMap (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) J f).val
      let aD := strictDualSliceCoefficient F hr ψ μN ν.val Wtest.val
        (modelMap (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F (reverse_sum h) σD) JD (E f)).val
      ∃! R : LaurentPolynomial ℂ,
        ofLaurentPolynomial R = (P₁ * P₂).toLaurent • a ∧
        ofLaurentPolynomial (laurentReflection q R) =
          (laurentReflection q
            (↑(clearedProductMultiplierUnit q (ζ₁ ^ r * c₁) d₁
              (ζ₂ ^ r * c₂) d₂)⁻¹ : LaurentPolynomial ℂ) *
                (P₁D * P₂D).toLaurent) • aD

set_option maxHeartbeats 1600000 in
/-- The two actual first-block laws and the proved lower Fourier identity
supply finite numerators. All factor witnesses precede every row and test. -/
theorem strictTwoBlockFiniteNumerators_of_laws
    [Measure.IsMulRightInvariant (unipotentHaar F t)]
    (hμN : IsCompatible (upperUnipotent (t + 1) F)
      (generalLinearHaar F t) (unipotentHaar F t) μN)
    (hπ : IsSmooth π)
    (hLaws : StrictTwoSidedFirstBlockLaws F h htr ψ ν π lambda σ hσ ell J μN μA μB) :
    StrictTwoBlockFiniteNumerators F h htr ψ ν π lambda σ ell hσ J μN μA μB := by
  let E := reversedDualSectionEquiv F h σ hσ
  let σD := fun i : Fin 2 => inverseTransposePullback (σ i.rev)
  let ellD := fun i : Fin 2 => secondDualFunctional ψ (σ i.rev) (ell i.rev)
  let JD := transportedSecondDualFunctional ψ (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) E J
  let q := strictResidueCardinalityUnit F
  obtain ⟨hOriginal, hReversed⟩ := hLaws
  obtain ⟨ζ₁, c₁, d₁, P₁, P₁D, hCert₁, hFirst⟩ := hOriginal
  obtain ⟨ζ₂, c₂, d₂, P₂D, P₂, hCert₂, hSecond⟩ := hReversed
  refine ⟨ζ₁, c₁, ζ₂, c₂, d₁, d₂, P₁, P₁D, P₂, P₂D, hCert₁, hCert₂, ?_⟩
  intro j k hr f Wtest
  dsimp only
  let WtestD := translatedFirstDualModelEquiv ψ π lambda (rightWeyl hr) Wtest
  let a := strictSliceCoefficient F hr ψ μN ν.val Wtest.val
    (modelMap (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) J f).val
  let aD := strictDualSliceCoefficient F hr ψ μN ν.val Wtest.val
    (modelMap (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F (reverse_sum h) σD) JD (E f)).val
  let b : BilateralLaurentSeries :=
    Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.kernelSliceCoefficient ν.val ell f Wtest.val μN hr
  let bD : BilateralLaurentSeries :=
    reversedDualSliceCoefficient F h σ hσ ψ ell hr f Wtest.val ν.val μN
  have hbD : bD = (Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.kernelSliceCoefficient ν.val ellD
      (E f) WtestD.val μN (by omega : r = t + (k + j + 1)) :
        BilateralLaurentSeries) := by
    rfl
  have hFirst' :
      Polynomial.eval₂ C (C ((q : ℂ)⁻¹) * T (-1)) P₁D • b =
        (C ((ζ₁ ^ r * c₁ : ℂˣ) : ℂ) * T d₁ * P₁.toLaurent) • a := by
    dsimp only [q, a, b]
    simpa only [coe_strictResidueCardinalityUnit, Units.val_mul,
      Units.val_pow_eq_pow_val] using hFirst j k hr f Wtest
  have hSecond' :
      Polynomial.eval₂ C (C ((q : ℂ)⁻¹) * T (-1)) P₂ • bD =
        (C ((ζ₂ ^ r * c₂ : ℂˣ) : ℂ) * T d₂ * P₂D.toLaurent) • aD := by
    rw [hbD]
    simpa only [q, aD, strictDualSliceCoefficient,
      negatedSelfDualHaar_val, coe_strictResidueCardinalityUnit, Units.val_mul,
      Units.val_pow_eq_pow_val, WtestD, translatedFirstDualModelEquiv_val,
      reversedDualTest] using hSecond k j (by omega) (E f) WtestD
  exact twoBlock_strictInducedCoefficient_numerators F h ψ σ hσ ell hr π hπ lambda J JD
    μN ν.val inferInstance hμN f Wtest (ζ₁ ^ r * c₁) d₁ (ζ₂ ^ r * c₂) d₂
    P₁ P₁D P₂ P₂D (by dsimp only [q, a, b] at hFirst'; exact hFirst')
      (by dsimp only [q, aD, bD] at hSecond'; exact hSecond')

omit σ ell hσ J μN μA μB in
/-- Above one real bound, a nonzero ordinary Jacquet functional supplies both
complete block certificates and finite numerators uniformly in the compatible
quotient measures. The independently owned analytic first-block statement is an explicit premise. -/
theorem exists_strictTwoBlockFiniteNumerators
    (H : TwoBlockDominantFirstBlockLaurentIdentityStatement.{uF,uV,uW})
    [Measure.IsMulRightInvariant (unipotentHaar F t)]
    [Measure.IsMulRightInvariant (unipotentHaar F (m 0))]
    [Measure.IsMulRightInvariant (unipotentHaar F (m 1))]
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hlambda : lambda.val ≠ 0)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (ell0 : ∀ i, glInverseFunctionals ψ (m i) (τ i))
    (hell0 : ∀ i, (ell0 i).val ≠ 0) :
    ∃ Cbound : ℝ, ∀ u : ℝ, Cbound < u →
      let σu := twoBlockOppositeTwistBlocks F m τ u
      let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i)
      let hσu : ∀ i, IsSmooth (σu i) := fun i =>
        ((twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u i _).2 (hτ i)).1.1
      let μR := rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)
      (∀ f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σu,
        Langlands.AllField.RankinSelberg.TwoBlockJacquet.IsAbsIntegrable ψ (fun i => (ell0 i).val) μR f) ∧
      ∃ Ju : glInverseFunctionals ψ t (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σu),
        Ju.val ≠ 0 ∧
        (∀ (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σu)
          (g : GeneralLinear (t + 1) F),
          Ju.val (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σu g f) =
            Langlands.AllField.RankinSelberg.TwoBlockJacquet.jacquetFunction ψ (fun i => (ellu i).val) μR f g) ∧
        ∀ (μN : Measure (LeftUnipotentQuotient t F))
          (μA : Measure (LeftUnipotentQuotient (m 0) F))
          (μB : Measure (LeftUnipotentQuotient (m 1) F)),
          IsCompatible (upperUnipotent (t + 1) F)
            (generalLinearHaar F t) (unipotentHaar F t) μN →
          IsCompatible (upperUnipotent (m 0 + 1) F)
            (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) μA →
          IsCompatible (upperUnipotent (m 1 + 1) F)
            (generalLinearHaar F (m 1)) (unipotentHaar F (m 1)) μB →
          StrictTwoBlockFiniteNumerators F h htr ψ ν π lambda σu ellu hσu Ju μN μA μB := by
  obtain ⟨Cbound, hCbound⟩ := exists_strictTwoSidedFirstBlockLaws F h htr ψ ν τ ell0
    π lambda H hπ hlambda hτ hell0
  refine ⟨Cbound, fun u hu => ?_⟩
  dsimp only
  obtain ⟨habs, Ju, hJu0, hJu, hLaws⟩ := hCbound u hu
  refine ⟨habs, Ju, hJu0, hJu, ?_⟩
  intro μN μA μB hμN hμA hμB
  exact strictTwoBlockFiniteNumerators_of_laws F h htr ψ ν π lambda
    (twoBlockOppositeTwistBlocks F m τ u)
    (fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i))
    (fun i => ((twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u i _).2
      (hτ i)).1.1)
    Ju μN μA μB hμN hπ.1.1
    (hLaws μN μA μB hμN hμA hμB)

end Langlands.AllField.RankinSelberg.DominantRankTransport
