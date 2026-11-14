import Langlands.Representation.RankinSelberg.TwoBlockDominantStrictRational
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantStrictContinuation
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantStrictFiniteNumerators
noncomputable section

namespace Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg.DominantRankTransport hiding EqualFirstBlockCoefficientLaw EqualLowerFourierCoefficientLaw EqualModelFiniteClearing EqualTwoSidedFirstBlockLaws StrictFirstBlockCoefficientLaw StrictFirstBlockFactorCertificate StrictModelFiniteClearing StrictTwoBlockFiniteNumerators StrictTwoBlockRationalComparison StrictTwoSidedFirstBlockLaws coe_strictResidueCardinalityUnit coefficientContinuationMatrixMeasurable coefficientContinuationQuotientMeasurable coefficientContinuationTopology determinantComplexPower_inverseTranspose determinantComplexPower_weylLong dualJacquetLocalField dualJacquetTopology dualJacquetValuation equalDualityBorel equalDualityGLBorel equalDualityGLMeasurable equalDualityLocalField equalDualityLowerBorel equalDualityLowerMeasurable equalDualityMeasurable equalDualityQuotientMeasurable equalDualityTopology equalDualityUnipotentBorel equalDualityUnipotentMeasurable equalDualityValuation equalFirstBlockBorel equalFirstBlockGLBorel equalFirstBlockGLMeasurable equalFirstBlockLocalField equalFirstBlockLowerMeasurable equalFirstBlockLowerSeries equalFirstBlockMeasurable equalFirstBlockQuotientMeasurable equalFirstBlockSecondCountable equalFirstBlockTopology equalFirstBlockUnipotentBorel equalFirstBlockUnipotentMeasurable equalFirstBlockValuation equalLowerFourierCoefficientLaw equalLowerGroupIntegrand_reversedDual equalLowerIntegrand_reversedDual equalModelFiniteClearing_polynomialDivisibility equalRank_hasBilateralSpectralExpansion equalSecondBlockBorel equalSecondBlockGLBorel equalSecondBlockGLMeasurable equalSecondBlockLocalField equalSecondBlockMeasurable equalSecondBlockQuotientMeasurable equalSecondBlockSecondCountable equalSecondBlockTopology equalSecondBlockUnipotentBorel equalSecondBlockUnipotentMeasurable equalSecondBlockValuation exists_equalFirstBlockBound_forOrdinaryFunctional exists_equalFirstBlockCoefficientLaw exists_equalTwoSidedFirstBlockLaws exists_reversedEqualFirstBlockBound exists_reversedStrictFirstBlockBound exists_strictFirstBlockBound_forOrdinaryFunctional exists_strictFirstBlockCoefficientLaw exists_strictTwoBlockFiniteNumerators exists_strictTwoSidedFirstBlockLaws instBorelSpaceCarrier instMeasurableSpaceCarrier instTopologicalSpaceCarrier lowerInduced_inverseWhittakerType negatedSelfDualHaar negatedSelfDualHaar_val radicalAverage_eq_equalRankIntegrand reversedDualBlocks_whittakerType reversedDualSectionEquiv_ordinary reversedDual_oppositeTwistBlocks secondDual_oppositeTwistFunctional_val strictCoefficientBorel strictCoefficientMeasurable strictCoefficientQuotientMeasurable strictCoefficientSecondCountable strictCoefficientTopology strictCoefficient_continuationData strictCoefficient_polynomialDivisibility strictContinuationGLBorel strictContinuationGLMeasurable strictContinuationLocalField strictContinuationMeasurable strictContinuationQuotientMeasurable strictContinuationSigmaCompact strictContinuationTopology strictContinuationUnipotentBorel strictContinuationUnipotentMeasurable strictContinuationValuation strictDualSliceCoefficient strictDualSliceCoefficient_lowerSupport strictFiniteNumeratorGLBorel strictFiniteNumeratorGLMeasurable strictFiniteNumeratorLocalField strictFiniteNumeratorLowerMeasurable strictFiniteNumeratorQuotientMeasurable strictFiniteNumeratorTopology strictFiniteNumeratorUnipotentBorel strictFiniteNumeratorUnipotentMeasurable strictFiniteNumeratorValuation strictFirstBlockGLBorel strictFirstBlockGLMeasurable strictFirstBlockLocalField strictFirstBlockLowerMeasurable strictFirstBlockQuotientMeasurable strictFirstBlockTopology strictFirstBlockUnipotentBorel strictFirstBlockUnipotentMeasurable strictFirstBlockValuation strictIntegral_eq strictModelFiniteClearing_polynomialDivisibility strictNumeratorGLBorel strictNumeratorGLMeasurable strictNumeratorGLTopology strictNumeratorLocalField strictNumeratorLowerMeasurable strictNumeratorMeasurable strictNumeratorQuotientMeasurable strictNumeratorTopology strictNumeratorUnipotentBorel strictNumeratorUnipotentMeasurable strictNumeratorValuation strictRankAnalyticAt strictRationalGLBorel strictRationalGLMeasurable strictRationalLocalField strictRationalQuotientMeasurable strictRationalTopology strictRationalUnipotentBorel strictRationalUnipotentMeasurable strictRationalValuation strictRectangleMeasure strictRectangleMeasure_sigmaFinite strictResidueCardinalityUnit strictSecondBlockGLBorel strictSecondBlockGLMeasurable strictSecondBlockLocalField strictSecondBlockQuotientMeasurable strictSecondBlockTopology strictSecondBlockUnipotentBorel strictSecondBlockUnipotentMeasurable strictSecondBlockValuation strictSliceCoefficient strictSliceCoefficient_lowerSupport strictTwoBlockFiniteNumerators_of_laws strictTwoBlockRationalComparison_of_numerators twoBlock_strictInducedCoefficient_numerators unequalRankSliceCoefficient_lowerSupport unequalRank_hasBilateralSpectralExpansion unfoldedJacquetSeries unfoldedJacquetSeries_eq
open Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg hiding AdjacentRankBaseModelStarIdentity AdjacentRankModelConvergenceStatement AdjacentRankModelStarStatement CharacterChangeCompatibleMeasureStatement EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankContinuedFormsStatement EqualRankFactorSwapStatement EqualRankFrobeniusStatement EqualRankFunctionalEquationStatement EqualRankLastRowReductionStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement EqualRankTrilinearUniquenessStatement EqualRankUnitValueStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement LowerFirstBlockIntegrationInputStatement LowerFirstBlockSliceTowerInputStatement NormalizedProductWhittakerTypeStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RankOneCharacterReductionStatement RankOneGammaTwistStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement RootTorusProductStatement SliceIntegrable SliceIntegrableAt SymmetricLPolynomialExistenceStatement TwoBlockDominantFirstBlockLaurentIdentityStatement TwoBlockDualSectionJacquetStatement TwoBlockFirstBlockLaurentIdentityStatement TwoBlockFirstBlockQuotientIntegrationStatement TwoBlockFixedSliceUnfoldingStatement TwoBlockGammaAdjacentRankStatement TwoBlockGammaDominantRankStatement TwoBlockGammaRankOneStatement TwoBlockJacquetConvergenceStatement TwoBlockLAdjacentRankStatement TwoBlockLDominantRankStatement TwoBlockLRankOneStatement TwoBlockLowerFirstBlockQuotientIntegrationStatement TwoBlockLowerFixedSliceConvergenceStatement TwoBlockOrdinaryJacquetFunctionalStatement TwoBlockUnipotentQuotientIntegrationStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UniformFiniteFunctionMellinConvergenceStatement UnipotentCharacterChangeModulusStatement WhittakerRowSliceCompactSupportStatement ZeroRowLastRowCutoffStatement adjacentRankFullFourier adjacentRankFullFourier_inverseTranspose adjacentRankFullFourier_tmul adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelStar adjacentRankModelStarBase_of_pure_integrals adjacentRankModelStarIntegrabilityLocalInstance1 adjacentRankModelStarIntegrabilityLocalInstance2 adjacentRankModelStarIntegrabilityLocalInstance3 adjacentRankModelStarIntegrabilityLocalInstance4 adjacentRankModelStarIntegrabilityLocalInstance5 adjacentRankModelStarIntegrabilityLocalInstance6 adjacentRankModelStarIntegrabilityLocalInstance7 adjacentRankModelStarIntegrabilityLocalInstance8 adjacentRankModelStarIntegrabilityLocalInstance9 adjacentRankModelStarSourceFunction_regularity adjacentRankModelStarTargetFunction_regularity adjacentRankModelStar_base adjacentRankModelStar_equality_of_base adjacentRankModelStar_pure_right_averages adjacentRankPure_hasCompactSupport adjacentRankTransformedIntegrand adjacentRankTransformedPure_hasCompactSupport adjacentRankTransformed_integrable_of_isSmooth adjacentRank_distribHaarChar adjacentRank_fullFourier_kernel_reflected_orbit adjacentRank_fullFourier_rowTranslate adjacentRank_inverseTranspose_unipotent_epsilon adjacentRank_kernel_reflected_right_orbit adjacentRank_kernel_right_unipotent adjacentRank_partialFourier_rowTranslate adjacentRank_rho0_kernel_right_orbit assembleLowerFirstBlockQuotientIntegration characterChangeCompatibleMeasure characterChangeCompatibleMeasure_of_unipotentModulus continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankAnalytic equalRankCompactRootExpansion equalRankContinuedForms equalRankFactorSwap equalRankFrobenius equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankLastRowReduction equalRankNormalizedCompactIntegration equalRankQuotientAnalytic equalRankRootAverageAnalytic equalRankRootExpansion equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport equalRankUnitValue exists_adjacentRank_lastColumn_bound exists_iwasawa_diagonal_le_of_simpleRoot exists_rankOneCutoff exists_rankOneEmbedding_support exists_schwartzBruhat_row_bound finiteFunctionMellin finiteFunctionShellSeries generalLinearDeterminantSlice hasCompactSupport_matrixSlice hasEqualRankCompactTest_of_kirillov hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClopen_generalLinearDeterminantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOfWhittakerType_quasicharacter_twist_iff isOpen_determinantSlice isPadicPairEpsilonFactor_swap_equalRank isPadicPairGammaFactor_swap_equalRank isPadicPairLPolynomial_swap_equalRank isPadicPairLPolynomial_twist isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricGammaFactor_rankOne_test_twist isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt isPadicSymmetricLPolynomial_rankOne_test_twist isPadicSymmetricLPolynomial_twist iwasawaTorusSum lastRowCompactOrbit leviModulus_characterChangeLevi leviModulus_characterChangeLevi_eq_pow lowerFirstBlockIntegrationInput_of_sliceTower lowerFirstBlockSliceTowerInput matrixSliceTest matrixSliceTest_apply measurableSet_determinantSlice mem_determinantSlice mem_generalLinearDeterminantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer modelStarBaseBorel modelStarBaseDisconnected modelStarBaseGLBorel modelStarBaseGLMeasurable modelStarBaseLocalField modelStarBaseMeasurable modelStarBaseT2 modelStarBaseTopology modelStarBaseUnipotentBorel modelStarBaseUnipotentMeasurable modelStarBaseValuative modelStarFourierBorel modelStarFourierDisconnected modelStarFourierLocalField modelStarFourierMeasurable modelStarFourierT2 modelStarFourierTopology modelStarFourierValuative modelStarOrbitFourierBorel modelStarOrbitFourierDisconnected modelStarOrbitFourierLocalField modelStarOrbitFourierMeasurable modelStarOrbitFourierSecondCountable modelStarOrbitFourierT2 modelStarOrbitFourierTopology modelStarOrbitFourierValuative modelStarReductionBorel modelStarReductionDisconnected modelStarReductionGLBorel modelStarReductionGLMeasurable modelStarReductionLocalField modelStarReductionMeasurable modelStarReductionT2 modelStarReductionTopology modelStarReductionValuative modelStarRegularityLocalField modelStarRegularityTopology modelStarRegularityValuative normalizedAbs_det_of_mem_generalLinearDeterminantSlice normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow normalizedProductWhittakerType oneVariableMellin padicPairGammaConstructionInput_iff padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType padic_quotient_sigmaFinite padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice quasicharacterSmoothCharacter quasicharacter_isOpen_ker quotientHaarExistence quotientIwasawaIntegration quotientRootIntegration rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneGammaTwist rankOneMatrixWhittakerComparison rankOneMatrixWhittakerComparison_of_positive rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct setIntegral_equalRankIntegrand_determinantSlice setIntegral_unequalRankAverage_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrableAt_unequalRankAverage_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice symmetricLPolynomialExists twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockDualSectionJacquet twoBlockFirstBlockLaurentIdentity twoBlockFirstBlockQuotientIntegration twoBlockFixedSliceUnfolding twoBlockGammaRankOne_of_trivial_test twoBlockJacquetConvergence twoBlockLRankOne_of_trivial_test twoBlockLowerFirstBlockQuotientIntegration twoBlockLowerFixedSliceConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val twoBlockOrdinaryJacquetFunctional twoBlockUnipotentQuotientIntegration unequalRankAnalytic unequalRankAverage unequalRankAverage_eq_mul_spectralPoint_zpow unequalRankCommonGenerator unequalRankCompactSupport unequalRankFiniteExpansion unequalRankFunctionalEquation unequalRankGammaPropagation unequalRankIntegrand_eq_mul_spectralPoint_zpow unequalRankIwasawaSupport unequalRankSliceCoefficient unequalRankSliceExpansion unequalRankSliceExpansion_of_converges unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unequalSliceMatrixMeasurable unequalSliceQuotientBorel unequalSliceQuotientMeasurable unequalSliceTopology unipotentCharacterChangeModulus unipotentHaar_mul_diagonal_le unipotentVolumeLocalField unipotentVolumeTopology unipotentVolumeValuativeRel whittakerRationalValues_eq_rankOneModelValues whittakerRowSliceCompactSupport zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory LaurentPolynomial
open Langlands.HarmonicAnalysis hiding AdjacentRankUnipotentFourierStatement PadicMatrixFourierSliceStatement PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement TwoBlockRowFourierCompanionStatement adjacentRankUnipotentFourier exists_rowSchwartz_order_lower_bound padicLatticeGeometry padicMatrixFourierSlice padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists padicUnipotentHaar_iota_fourier_duality_right twoBlockRowFourierCompanion
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding CompactLocalizationStatement MirabolicCompactTwistedPairingStatement MirabolicFiniteLengthStatement MirabolicFunctionalMultiplicityStatement MirabolicTwistedPairingRigidityStatement MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier UnipotentOrbitStatement compactLocalization exchangedParabolic exists_compactOpen_glCoefficientRightStabilizer functionalsCongr hasCompactSupport_twoBlockCellRestriction inducedLocalization_of_prerequisites mirabolicCompactTwistedPairing mirabolicFiniteLength mirabolicFunctionalMultiplicity mirabolicUnitTest modelKirillovTransfer mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentOrbit unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding blockRotation_inv_mem_integralOpen blockRotation_inv_mul_mem_integralOpen blockRotation_mem_integralOpen canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockDominantRectangular hiding AbsoluteInput FiberIntegrable KernelAbsoluteIntegrable KernelNormProfileIntegrable KernelOuterIntegrable NormProfileIntegrable OuterIntegrable absoluteInput_standard_iff ae_lowerQuotientMeasure_iff ae_quotientFiberIntegrable_spectral_iff determinantWeight_lowerBlockUnipotent_mul dualKernelLocalField dualKernelMeasurable dualKernelTopology dualKernelValuation dualRectangleBorel dualRectangleLocalField dualRectangleMatrixBorel dualRectangleMatrixSecondCountable dualRectangleMeasurable dualRectangleProductBorel dualRectangleSecondCountable dualRectangleTopology dualRectangleValuation dualSlicesGLBorel dualSlicesGLMeasurable dualSlicesGLTopologicalGroup dualSlicesLocalField dualSlicesLowerBorel dualSlicesLowerMeasurable dualSlicesMeasurable dualSlicesStandardMeasurable dualSlicesTopology dualSlicesUnipotentBorel dualSlicesUnipotentMeasurable dualSlicesValuation fiberIntegrable_lowerBlockUnipotent_mul_iff fiberIntegrable_spectral_iff integrableOn_quotientKernel_spectral_iff integrableOn_quotientNormProfile_spectral_iff integrable_lowerQuotientMeasure_iff integrable_rectangleChange_iff integral_dualRectangleEquiv integral_rectangleChange kernel kernelAbsoluteIntegrable_iff kernelAbsoluteIntegrable_restrict_spectral_iff kernelAbsoluteIntegrable_standard_iff kernelSliceCoefficient kernel_covariance kernel_eq kernel_reversedDual kernel_spectral lowerDuality_restrict_measurePreserving measurePreserving_dualRectangleEquiv measurePreserving_rectangleChange outerFieldT2 outerFieldTopology outerFieldValuation outerGeneralLinearGroup outerGeneralLinearLocallyCompact outerGeneralLinearSecondCountable outerLocalField quotientFiberIntegrable quotientFiberIntegrable_spectral_iff quotientKernel quotientKernelMeasurable quotientKernelTopology quotientKernel_mk quotientKernel_reversedDual quotientKernel_spectral quotientKernel_spectral_onSlice quotientNormProfile quotientNormProfile_mk quotientNormProfile_spectral quotientNormProfile_spectral_onSlice rawKernel rawKernel_covariance rawKernel_reversedDual rawScalarValue rectangleChangeHomeomorph rectangleHaarBorel rectangleHaarLocalField rectangleHaarMeasurable rectangleHaarSecondCountable rectangleHaarTopology rectangleHaarValuation rectangleMatrixBorel rectangleMatrixSecondCountable rectangleMeasure rectangleMeasure_sigmaFinite rectanglesBorel representativeKernel representativeKernel_lowerBlockUnipotent_mul representativeKernel_reversedDual representativeKernel_spectral representativeNormProfile representativeNormProfile_lowerBlockUnipotent_mul representativeNormProfile_spectral reversedDualSectionEquiv reversedDualSectionEquiv_scalar reversedDualSliceCoefficient reversedDualSliceCoefficient_eq setIntegral_quotientKernel_reversedDual setIntegral_quotientKernel_spectral sliceSpectralMeasurable sliceSpectralTopology standardCompatible standardCompatible_sigmaFinite
open Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.LocalFactor
open Langlands.AllField.LocalFactor
open Langlands.HarmonicAnalysis.BilateralLaurentSeries

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance strictRationalT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance strictRationalSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance strictRationalMeasurable : MeasurableSpace F := borel _
local instance strictRationalBorel : BorelSpace F := ⟨rfl⟩
local instance strictRationalGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance strictRationalGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance strictRationalUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance strictRationalUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
local instance strictRationalQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F) := borel _
local instance strictRationalQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩

variable {t r : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
  [hmod : ∀ i, Module ℂ (W i)]

local notation "qF" => (Langlands.LocalFieldData.residueCardinality (⟨⟩ : LocalFieldData F))
local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

variable (htr : t < r) (ψ : UnitaryAdditiveCharacter F)
  (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (r + 1) F) V)
  (lambda : glFunctionals ψ r π)
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
  (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
  (hσ : ∀ i, IsSmooth (σ i))
  (J : glInverseFunctionals ψ t (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ))
  (μN : Measure (LeftUnipotentQuotient t F))
  (μA : Measure (LeftUnipotentQuotient (m 0) F))
  (μB : Measure (LeftUnipotentQuotient (m 1) F))

/-- Actual strict original and reversed rational integrals, with retained
complete block certificates, uniform clearing and every intrinsic L bound. -/
def StrictTwoBlockRationalComparison : Prop :=
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
    (∀ (j k : ℕ) (hr : r = t + (j + k + 1))
      (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σ)
      (Wtest : (coefficientModel π lambda).toSubmodule),
      ∃ R RD : RationalFunctions,
        HasRationalContinuation qF
          (unequalRankIntegralAt j k hr ψ abv μN
            (rectangularMeasure ν.val j (t + 1)) Wtest.val
            (modelMap (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) J f).val) R ∧
        HasRationalContinuation qF
          (unequalRankIntegralAt k j (by omega) (ψ.scale (-1)) abv μN
            (rectangularMeasure ν.val k (t + 1)) (reversedDualTest hr ψ Wtest.val)
            (modelMap (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F (reverse_sum h) σD) JD (E f)).val) RD ∧
        RationalReflection.subst q⁻¹
            (laurentToRatFunc (P₁D * P₂D).toLaurent * RD) =
          laurentToRatFunc
              (↑(clearedProductMultiplierUnit q (ζ₁ ^ r * c₁) d₁
                (ζ₂ ^ r * c₂) d₂) : LaurentPolynomial ℂ) *
            laurentToRatFunc (P₁ * P₂).toLaurent * R) ∧
    (∀ (j k : ℕ) (hr : r = t + (j + k + 1))
      (U : (coefficientModel π lambda).toSubmodule)
      (U' : (coefficientModel (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) J).toSubmodule),
      ∃ N : LaurentPolynomial ℂ,
        ofLaurentPolynomial N = (P₁ * P₂).toLaurent •
          strictSliceCoefficient F hr ψ μN ν.val U.val U'.val) ∧
    ∀ (j k : ℕ) (hr : r = t + (j + k + 1)) (P : Polynomial ℂ),
      IsNormalizedGenerator
        (unequalRankZetaValuesAt j k hr qF ψ abv μN
          (rectangularMeasure ν.val j (t + 1)) π (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ)) P →
      ∃ (Q : Polynomial ℂ) (e : ℕ), Polynomial.X ^ e * (P₁ * P₂) = Q * P

set_option maxHeartbeats 1600000 in
/-- Actual spectral expansions turn the finite numerators into rational
identities. Surjectivity onto the fixed induced model gives the intrinsic
L-polynomial bound at every complementary row. -/
theorem strictTwoBlockRationalComparison_of_numerators
    [Measure.IsMulRightInvariant (unipotentHaar F t)]
    (hμN : IsCompatible (upperUnipotent (t + 1) F)
      (generalLinearHaar F t) (unipotentHaar F t) μN)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσtype : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (hlambda : lambda.val ≠ 0) (hJ0 : J.val ≠ 0)
    (hnum : StrictTwoBlockFiniteNumerators F h htr ψ ν π lambda σ ell hσ J μN μA μB) :
    StrictTwoBlockRationalComparison F h htr ψ ν π lambda σ ell hσ J μN μA μB := by
  let E := reversedDualSectionEquiv F h σ hσ
  let σD := fun i : Fin 2 => inverseTransposePullback (σ i.rev)
  let JD := transportedSecondDualFunctional ψ (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) E J
  let q := strictResidueCardinalityUnit F
  obtain ⟨ζ₁, c₁, ζ₂, c₂, d₁, d₂, P₁, P₁D, P₂, P₂D,
    hcert₁, hcert₂, hfinite⟩ := hnum
  have hInd := lowerInduced_inverseWhittakerType F h ψ σ hσtype
  have hπD := isOfWhittakerType_firstDual ψ π hπ
  have hσD := reversedDualBlocks_whittakerType F σ ψ hσtype
  have hIndD := lowerInduced_inverseWhittakerType F (reverse_sum h)
    (ψ.scale (-1)) σD hσD
  have hclear : ∀ (j k : ℕ) (hr : r = t + (j + k + 1))
      (U : (coefficientModel π lambda).toSubmodule)
      (U' : (coefficientModel (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) J).toSubmodule),
      ∃ N : LaurentPolynomial ℂ,
        ofLaurentPolynomial N = (P₁ * P₂).toLaurent •
          strictSliceCoefficient F hr ψ μN ν.val U.val U'.val := by
    intro j k hr U U'
    obtain ⟨f, hf⟩ := modelMap_surjective (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) J U'
    obtain ⟨N, hN, -⟩ := hfinite j k hr f U
    exact ⟨N, by simpa only [hf] using hN.1⟩
  have hP₁ : P₁ ≠ 0 := by
    have hblock : m 0 < r := lt_trans (firstBlock_lt_total h) htr
    exact (hcert₁.2.2 0 (r - m 0 - 1) (by omega)).1.polynomial_ne_zero
  have hP₂ : P₂ ≠ 0 := by
    have hsum : (m 0 + 1) + (m 1 + 1) = t + 1 := by
      simpa only [Fin.sum_univ_two] using h
    have hblock : m 1 < r := by omega
    exact (hcert₂.2.2 0 (r - m 1 - 1) (by
      change r = m 1 + (0 + (r - m 1 - 1) + 1)
      omega)).2.polynomial_ne_zero
  refine ⟨ζ₁, c₁, ζ₂, c₂, d₁, d₂, P₁, P₁D, P₂, P₂D,
    hcert₁, hcert₂, ?_, hclear, ?_⟩
  · intro j k hr f Wtest
    let U' := modelMap (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) J f
    let UD := translatedFirstDualModelEquiv ψ π lambda (rightWeyl hr) Wtest
    let U'D := modelMap (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F (reverse_sum h) σD) JD (E f)
    obtain ⟨hexp, R, hR⟩ := strictCoefficient_continuationData F hr ψ μN ν.val π
      (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) lambda J hμN hπ hInd hlambda hJ0 Wtest U'
    obtain ⟨hexpD, RD, hRD⟩ := strictCoefficient_continuationData F
      (by omega : r = t + (k + j + 1)) (ψ.scale (-1)) μN ν.val
      (inverseTransposePullback π) (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F (reverse_sum h) σD)
      (firstDualFunctional ψ π lambda) JD hμN hπD hIndD
      (firstDualFunctional_ne_zero ψ π hlambda)
      (transportedSecondDualFunctional_ne_zero ψ (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) E hJ0)
      UD U'D
    refine ⟨R, RD, hR, hRD, ?_⟩
    obtain ⟨N, hN, -⟩ := hfinite j k hr f Wtest
    exact reflectedNumerators_rationalIdentity
      (⟨⟩ : LocalFieldData F).residueCardinality_gt_one q
      (P₁ * P₂).toLaurent (P₁D * P₂D).toLaurent
      (clearedProductMultiplierUnit q (ζ₁ ^ r * c₁) d₁ (ζ₂ ^ r * c₂) d₂) R RD
      hexp hexpD ⟨N, hN⟩ hR hRD
  · intro j k hr P hP
    exact strictCoefficient_polynomialDivisibility F hr ψ μN ν.val π
      (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) lambda J hπ hInd hlambda hJ0
      P (P₁ * P₂) (mul_ne_zero hP₁ hP₂) hP (hclear j k hr)

end Langlands.AllField.RankinSelberg.DominantRankTransport
