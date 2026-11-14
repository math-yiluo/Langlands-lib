import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualLContinuation
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankClearingKernel
import Langlands.AllField.Representation.RankinSelberg.PadicPairLPolynomialNormalization
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantEqualEntireSlices
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantEqualFactors
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantOppositeDeformation
noncomputable section

namespace Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg.DominantRankTransport hiding EqualFirstBlockCoefficientLaw EqualFirstBlockFactorCertificate EqualFirstBlockSymmetricFactors EqualLowerFourierCoefficientLaw EqualModelFiniteClearing EqualOppositeRealRayClearing EqualRankEntireSliceData EqualTwoBlockFiniteNumerators EqualTwoBlockRationalComparison EqualTwoBlockSymmetricLBound EqualTwoSidedFirstBlockLaws OppositeWhittakerFamilyData StrictModelFiniteClearing ambient_mul_firstBlock_eq_opposite coe_equalResidueCardinalityUnit coefficientContinuationMatrixMeasurable coefficientContinuationQuotientMeasurable coefficientContinuationTopology complexOppositeTwistBlocks complexOppositeTwistInduced complexOppositeTwistInduced_inverseWhittakerType determinantComplexPower_inverseTranspose determinantComplexPower_weylLong dualJacquetLocalField dualJacquetTopology dualJacquetValuation equalDualityBorel equalDualityGLBorel equalDualityGLMeasurable equalDualityLocalField equalDualityLowerBorel equalDualityLowerMeasurable equalDualityMeasurable equalDualityQuotientMeasurable equalDualityTopology equalDualityUnipotentBorel equalDualityUnipotentMeasurable equalDualityValuation equalEntireLocalField equalEntireQuotientBorel equalEntireQuotientMeasurable equalEntireTopology equalEntireValuation equalFactorsGLBorel equalFactorsGLMeasurable equalFactorsLocalField equalFactorsMeasurable equalFactorsQuotientBorel equalFactorsQuotientMeasurable equalFactorsTopology equalFactorsUnipotentBorel equalFactorsUnipotentMeasurable equalFactorsValuation equalFirstBlockBorel equalFirstBlockGLBorel equalFirstBlockGLMeasurable equalFirstBlockLocalField equalFirstBlockLowerMeasurable equalFirstBlockLowerSeries equalFirstBlockMeasurable equalFirstBlockQuotientMeasurable equalFirstBlockSecondCountable equalFirstBlockTopology equalFirstBlockUnipotentBorel equalFirstBlockUnipotentMeasurable equalFirstBlockValuation equalLContinuationGLBorel equalLContinuationGLMeasurable equalLContinuationLocalField equalLContinuationQuotientBorel equalLContinuationQuotientMeasurable equalLContinuationTopology equalLContinuationUnipotentBorel equalLContinuationUnipotentMeasurable equalLContinuationValuation equalLowerFourierCoefficientLaw equalLowerGroupIntegrand_reversedDual equalLowerIntegrand_reversedDual equalModelFiniteClearing_polynomialDivisibility equalNumeratorGLBorel equalNumeratorGLMeasurable equalNumeratorLocalField equalNumeratorQuotientMeasurable equalNumeratorTopology equalNumeratorUnipotentBorel equalNumeratorUnipotentMeasurable equalNumeratorValuation equalRankCoefficient_clearing_of_certificate equalRankCoefficient_continuationData equalRankEntireSliceData equalRank_hasBilateralSpectralExpansion equalRationalGLBorel equalRationalGLMeasurable equalRationalLocalField equalRationalQuotientMeasurable equalRationalTopology equalRationalUnipotentBorel equalRationalUnipotentMeasurable equalRationalValuation equalResidueCardinalityUnit equalSecondBlockBorel equalSecondBlockGLBorel equalSecondBlockGLMeasurable equalSecondBlockLocalField equalSecondBlockMeasurable equalSecondBlockQuotientMeasurable equalSecondBlockSecondCountable equalSecondBlockTopology equalSecondBlockUnipotentBorel equalSecondBlockUnipotentMeasurable equalSecondBlockValuation equalTwoBlockFiniteNumerators_of_laws equalTwoBlockRationalComparison_of_numerators equalTwoBlockSymmetricLBound_at_zero equalTwoBlockSymmetricLBound_of_rationalComparison exists_equalFirstBlockBound_forOrdinaryFunctional exists_equalFirstBlockCoefficientLaw exists_equalOppositeRealRayClearing exists_equalTwoBlockFiniteNumerators exists_equalTwoBlockRationalComparison exists_equalTwoBlockSymmetricLBound exists_equalTwoSidedFirstBlockLaws exists_oppositeWhittakerFamily exists_opposite_coefficient exists_reversedEqualFirstBlockBound firstBlockZeroComparison instBorelSpaceCarrier instMeasurableSpaceCarrier instTopologicalSpaceCarrier lowerInduced_inverseWhittakerType negatedSelfDualHaar negatedSelfDualHaar_val oppositeDeformationTopology oppositeTwistComparison radicalAverage_eq_equalRankIntegrand reversedDualBlocks_whittakerType reversedDualSectionEquiv_ordinary reversedDual_oppositeTwistBlocks secondDual_oppositeTwistFunctional_val strictModelFiniteClearing_polynomialDivisibility symmetricFactors_of_modelCertificates symmetricLPolynomial_of_modelGenerator unequalRank_hasBilateralSpectralExpansion unfoldedJacquetSeries unfoldedJacquetSeries_eq
open Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg hiding AdjacentRankBaseModelStarIdentity AdjacentRankModelConvergenceStatement AdjacentRankModelStarStatement CentralBilinearVanishingStatement CharacterChangeCompatibleMeasureStatement CorankOneEntireSliceStatement EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankContinuedFormsStatement EqualRankFactorSwapStatement EqualRankFrobeniusStatement EqualRankFunctionalEquationStatement EqualRankGammaExistenceStatement EqualRankLastRowReductionStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement EqualRankTrilinearMirabolicPrerequisites EqualRankTrilinearPrerequisites EqualRankTrilinearUniquenessStatement EqualRankUnitValueStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement LowerFirstBlockIntegrationInputStatement LowerFirstBlockSliceTowerInputStatement NormalizedProductWhittakerTypeStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RankOneCharacterReductionStatement RankOneGammaTwistStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement RootTorusProductStatement SliceIntegrable SliceIntegrableAt SymmetricLPolynomialExistenceStatement TwoBlockDualSectionJacquetStatement TwoBlockFirstBlockLaurentIdentityStatement TwoBlockFirstBlockQuotientIntegrationStatement TwoBlockFixedSliceUnfoldingStatement TwoBlockGammaAdjacentRankStatement TwoBlockGammaDominantRankStatement TwoBlockGammaRankOneStatement TwoBlockJacquetConvergenceStatement TwoBlockLAdjacentRankStatement TwoBlockLDominantRankStatement TwoBlockLRankOneStatement TwoBlockLowerFirstBlockQuotientIntegrationStatement TwoBlockLowerFixedSliceConvergenceStatement TwoBlockOrdinaryJacquetFunctionalStatement TwoBlockSecondWhittakerDeformationStatement TwoBlockUnipotentQuotientIntegrationStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UniformFiniteFunctionMellinConvergenceStatement UnipotentCharacterChangeModulusStatement UnramifiedTwistLFactorStatement WhittakerRowSliceCompactSupportStatement WhittakerTypeGammaConstructionInputStatement ZeroRowLastRowCutoffStatement adjacentRankFullFourier adjacentRankFullFourier_inverseTranspose adjacentRankFullFourier_tmul adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelStar adjacentRankModelStarBase_of_pure_integrals adjacentRankModelStarIntegrabilityLocalInstance1 adjacentRankModelStarIntegrabilityLocalInstance2 adjacentRankModelStarIntegrabilityLocalInstance3 adjacentRankModelStarIntegrabilityLocalInstance4 adjacentRankModelStarIntegrabilityLocalInstance5 adjacentRankModelStarIntegrabilityLocalInstance6 adjacentRankModelStarIntegrabilityLocalInstance7 adjacentRankModelStarIntegrabilityLocalInstance8 adjacentRankModelStarIntegrabilityLocalInstance9 adjacentRankModelStarSourceFunction_regularity adjacentRankModelStarTargetFunction_regularity adjacentRankModelStar_base adjacentRankModelStar_equality_of_base adjacentRankModelStar_pure_right_averages adjacentRankPure_hasCompactSupport adjacentRankTransformedIntegrand adjacentRankTransformedPure_hasCompactSupport adjacentRankTransformed_integrable_of_isSmooth adjacentRank_distribHaarChar adjacentRank_fullFourier_kernel_reflected_orbit adjacentRank_fullFourier_rowTranslate adjacentRank_inverseTranspose_unipotent_epsilon adjacentRank_kernel_reflected_right_orbit adjacentRank_kernel_right_unipotent adjacentRank_partialFourier_rowTranslate adjacentRank_rho0_kernel_right_orbit assembleLowerFirstBlockQuotientIntegration centralBilinearVanishing centralSpectralElement centralSpectralElement_det_abs centralSpectralElement_mem_center characterChangeCompatibleMeasure characterChangeCompatibleMeasure_of_unipotentModulus continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice determinantWeight_centralSpectralElement diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankAnalytic equalRankCompactRootExpansion equalRankContinuedForms equalRankFactorSwap equalRankFrobenius equalRankFunctionalEquation equalRankGammaExistence equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankLastRowReduction equalRankNormalizedCompactIntegration equalRankQuotientAnalytic equalRankRootAverageAnalytic equalRankRootExpansion equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport equalRankTrilinearPrerequisites_of_mirabolic equalRankTrilinearUniqueness equalRankTrilinearUniqueness_of_mirabolic_prerequisites equalRankTrilinearUniqueness_of_prerequisites equalRankUnitValue exists_adjacentRank_lastColumn_bound exists_iwasawa_diagonal_le_of_simpleRoot exists_rankOneCutoff exists_rankOneEmbedding_support exists_schwartzBruhat_row_bound finiteFunctionMellin finiteFunctionShellSeries generalLinearDeterminantSlice hasCompactSupport_matrixSlice hasEqualRankCompactTest_of_kirillov hasSum_setIntegral_determinantSlice iUnion_determinantSlice inverseUniformizer_normalizedAbsoluteValue isClopen_determinantSlice isClopen_generalLinearDeterminantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOfWhittakerType_quasicharacter_twist_iff isOpen_determinantSlice isPadicPairEpsilonFactor_swap_equalRank isPadicPairGammaFactor_swap_equalRank isPadicPairLPolynomial_swap_equalRank isPadicPairLPolynomial_twist isPadicPairLPolynomial_unramified_of_transport isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricGammaFactor_rankOne_test_twist isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt isPadicSymmetricLPolynomial_rankOne_test_twist isPadicSymmetricLPolynomial_twist isPadicSymmetricLPolynomial_unramified_of_transport iwasawaTorusSum lastRowCompactOrbit leviModulus_characterChangeLevi leviModulus_characterChangeLevi_eq_pow lowerFirstBlockIntegrationInput_of_sliceTower lowerFirstBlockSliceTowerInput matrixSliceTest matrixSliceTest_apply measurableSet_determinantSlice mem_determinantSlice mem_generalLinearDeterminantSlice mirabolic_exists_exception_length_le_one mirabolic_pair_control_of_statements mirabolic_shift_length_bound mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer modelStarBaseBorel modelStarBaseDisconnected modelStarBaseGLBorel modelStarBaseGLMeasurable modelStarBaseLocalField modelStarBaseMeasurable modelStarBaseT2 modelStarBaseTopology modelStarBaseUnipotentBorel modelStarBaseUnipotentMeasurable modelStarBaseValuative modelStarFourierBorel modelStarFourierDisconnected modelStarFourierLocalField modelStarFourierMeasurable modelStarFourierT2 modelStarFourierTopology modelStarFourierValuative modelStarOrbitFourierBorel modelStarOrbitFourierDisconnected modelStarOrbitFourierLocalField modelStarOrbitFourierMeasurable modelStarOrbitFourierSecondCountable modelStarOrbitFourierT2 modelStarOrbitFourierTopology modelStarOrbitFourierValuative modelStarReductionBorel modelStarReductionDisconnected modelStarReductionGLBorel modelStarReductionGLMeasurable modelStarReductionLocalField modelStarReductionMeasurable modelStarReductionT2 modelStarReductionTopology modelStarReductionValuative modelStarRegularityLocalField modelStarRegularityTopology modelStarRegularityValuative normalizedAbs_det_of_mem_generalLinearDeterminantSlice normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow normalizedProductWhittakerType oneVariableMellin padicPairGammaConstructionInput_iff padicPairGammaConstructionInput_of_whittakerType padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType padic_quotient_sigmaFinite padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice quasicharacterSmoothCharacter quasicharacter_isOpen_ker quotientHaarExistence quotientIwasawaIntegration quotientRootIntegration rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneGammaTwist rankOneMatrixWhittakerComparison rankOneMatrixWhittakerComparison_of_positive rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct setIntegral_equalRankIntegrand_determinantSlice setIntegral_unequalRankAverage_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrableAt_unequalRankAverage_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice symmetricLPolynomialExists twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockDualSectionJacquet twoBlockFirstBlockLaurentIdentity twoBlockFirstBlockQuotientIntegration twoBlockFixedSliceUnfolding twoBlockGammaRankOne_of_trivial_test twoBlockJacquetConvergence twoBlockLRankOne_of_trivial_test twoBlockLowerFirstBlockQuotientIntegration twoBlockLowerFixedSliceConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val twoBlockOrdinaryJacquetFunctional twoBlockSecondDeformedBlocks twoBlockSecondDeformedBlocks_zero twoBlockSecondDeformedInduced twoBlockSecondWhittakerDeformation twoBlockUnipotentQuotientIntegration twoBlockWhittakerDeformation unequalRankAnalytic unequalRankAverage unequalRankAverage_eq_mul_spectralPoint_zpow unequalRankCommonGenerator unequalRankCompactSupport unequalRankFiniteExpansion unequalRankFunctionalEquation unequalRankGammaPropagation unequalRankIntegrand_eq_mul_spectralPoint_zpow unequalRankIwasawaSupport unequalRankSliceCoefficient unequalRankSliceExpansion unequalRankSliceExpansion_of_converges unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unequalSliceMatrixMeasurable unequalSliceQuotientBorel unequalSliceQuotientMeasurable unequalSliceTopology unipotentCharacterChangeModulus unipotentHaar_mul_diagonal_le unipotentVolumeLocalField unipotentVolumeTopology unipotentVolumeValuativeRel unramifiedTwistLFactor unramifiedTwistLFactor_of_transport whittakerRationalValues_eq_rankOneModelValues whittakerRowSliceCompactSupport whittakerTypeGammaConstructionInput zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Polynomial
open Langlands.HarmonicAnalysis hiding AdjacentRankUnipotentFourierStatement PadicMatrixFourierSliceStatement PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement TwoBlockRowFourierCompanionStatement adjacentRankUnipotentFourier exists_rowSchwartz_order_lower_bound padicLatticeGeometry padicMatrixFourierSlice padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists padicUnipotentHaar_iota_fourier_duality_right twoBlockRowFourierCompanion
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding CompactLocalizationStatement MirabolicCompactTwistedPairingStatement MirabolicFiniteLengthStatement MirabolicFunctionalMultiplicityStatement MirabolicTwistedPairingRigidityStatement MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier UnipotentOrbitStatement compactLocalization exchangedParabolic exists_compactOpen_glCoefficientRightStabilizer functionalsCongr hasCompactSupport_twoBlockCellRestriction inducedLocalization_of_prerequisites mirabolicCompactTwistedPairing mirabolicFiniteLength mirabolicFunctionalMultiplicity mirabolicTwistedPairingRigidity mirabolicUnitTest modelKirillovTransfer mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentOrbit unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding blockRotation_inv_mem_integralOpen blockRotation_inv_mul_mem_integralOpen blockRotation_mem_integralOpen canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance equalLContinuationT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance equalLContinuationMeasurable : MeasurableSpace F := borel _
local instance equalLContinuationBorel : BorelSpace F := ⟨rfl⟩
local instance equalLContinuationGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance equalLContinuationGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance equalLContinuationUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance equalLContinuationUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
local instance equalLContinuationQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F) := borel _
local instance equalLContinuationQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩

local notation "qF" => (Langlands.LocalFieldData.residueCardinality (⟨⟩ : LocalFieldData F))
local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

open Langlands.RankinSelberg.ParameterSpecialization
open Langlands.HarmonicAnalysis.BilateralLaurentSeries
open Langlands.RankinSelberg.AdjacentGammaContinuation

section Coefficients

variable {n : ℕ} (ψ : UnitaryAdditiveCharacter F)
  (μ : Measure (LeftUnipotentQuotient n F))
  [Measure.IsMulRightInvariant (unipotentHaar F n)]
  (hμ : IsCompatible (upperUnipotent (n + 1) F)
    (generalLinearHaar F n) (unipotentHaar F n) μ)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {U : Type uW} [AddCommGroup U] [Module ℂ U]
  (π : Representation ℂ (GeneralLinear (n + 1) F) V)
  (τ : Representation ℂ (GeneralLinear (n + 1) F) U)
  (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
  (hτ : IsOfWhittakerType n (inverseStandardCharacter ψ n) τ)
  (lambda : glFunctionals ψ n π) (ell : glInverseFunctionals ψ n τ)
  (hlambda : lambda.val ≠ 0) (hell : ell.val ≠ 0)
  (f : (coefficientModel π lambda).toSubmodule)
  (f' : (coefficientModel τ ell).toSubmodule)
  (Φ : SchwartzBruhat (Fin (n + 1) → F))

include hμ hπ hτ hlambda hell

/-- Full type supplies a rational continuation and an absolute expansion
of the same actual equal-rank integral. -/
theorem equalRankCoefficient_continuationData :
    ∃ R : RationalFunctions,
      HasRationalContinuation qF
        (fun s => equalRankIntegral ψ abv μ f.val f'.val Φ s) R ∧
      HasAbsoluteBilateralSpectralExpansion qF
        (equalRankSliceCoefficient (⟨⟩ : LocalFieldData F) μ ψ f.val f'.val Φ)
        (fun s => equalRankIntegral ψ abv μ f.val f'.val Φ s) := by
  have han := equalRankAnalytic F (⟨⟩ : LocalFieldData F) n ψ μ hμ
    V U π τ hπ hτ lambda ell hlambda hell
  obtain ⟨R, hR⟩ := han.2.1 f f' Φ
  obtain ⟨C, hC⟩ := han.1 f f' Φ
  exact ⟨R, hR, C, fun s hs =>
    (equalRankSliceExpansion F (⟨⟩ : LocalFieldData F) n μ ψ f.val f'.val Φ s
      (hC s hs)).2⟩

/-- A complete L certificate and its polynomial divisibility clear each
actual equal-rank coefficient vector, by scalar spectral uniqueness. -/
theorem equalRankCoefficient_clearing_of_certificate
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (P A : Polynomial ℂ) (hA : A ≠ 0)
    (hP : IsPadicSymmetricLPolynomial F ψ ν.val π τ P)
    (hdiv : ∃ (Q : Polynomial ℂ) (e : ℕ), X ^ e * A = Q * P) :
    let a : BilateralLaurentSeries :=
      equalRankSliceCoefficient (⟨⟩ : LocalFieldData F) μ ψ f.val f'.val Φ
    ∃ L : LaurentPolynomial ℂ, ofLaurentPolynomial L = A.toLaurent • a := by
  have hgen : IsNormalizedGenerator (equalRankZetaValues qF ψ abv μ π τ) P :=
    isPairLPolynomial_self.mp (((isPadicSymmetricLPolynomial_of_le (le_refl n)).mp hP).2 μ hμ)
  have hspan : Submodule.span LaurentCoefficients
      {(algebraMap (Polynomial ℂ) RationalFunctions P)⁻¹} ≤
      Submodule.span LaurentCoefficients
        {(algebraMap (Polynomial ℂ) RationalFunctions A)⁻¹} :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr
      ((reciprocalLaurentSpanClearing P A hgen.polynomial_ne_zero hA).mpr hdiv)
  have han := equalRankAnalytic F (⟨⟩ : LocalFieldData F) n ψ μ hμ
    V U π τ hπ hτ lambda ell hlambda hell
  obtain ⟨R, hR, ha⟩ := equalRankCoefficient_continuationData F ψ μ hμ
    π τ hπ hτ lambda ell hlambda hell f f' Φ
  have hmem : R ∈ Submodule.span LaurentCoefficients
      {(algebraMap (Polynomial ℂ) RationalFunctions A)⁻¹} := by
    apply hspan
    rw [← hgen.2]
    exact mem_zetaSpan (equalRankModel_mem_zetaValues qF ψ abv μ
      lambda ell f f' Φ (han.1 f f' Φ) hR)
  obtain ⟨L, hL⟩ := Submodule.mem_span_singleton.mp hmem
  have hclear : laurentToRatFunc L = algebraMap (Polynomial ℂ) RationalFunctions A * R := by
    rw [← hL, Algebra.smul_def, algebraMap_laurent]
    rw [mul_left_comm, mul_inv_cancel₀ (RatFunc.algebraMap_ne_zero hA), mul_one]
  exact ⟨L, (TwoBlockFirstBlockLaurent.cleared_series_eq
    (⟨⟩ : LocalFieldData F).residueCardinality_gt_one hclear hR ha).symm⟩

end Coefficients

section Blocks

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  (ψ : UnitaryAdditiveCharacter F)
  (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (t + 1) F) V)
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))

/-- The actual opposite lower induction retains full inverse Whittaker type
at every complex parameter. -/
theorem complexOppositeTwistInduced_inverseWhittakerType
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (u : ℂ) :
    IsOfWhittakerType t (inverseStandardCharacter ψ t)
      (complexOppositeTwistInduced F m h σ u) := by
  have hu : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i))
      (complexOppositeTwistBlocks F m σ u i) := by
    intro i
    exact (isOfWhittakerType_twist_iff _ _ (σ i)
      ((⟨⟩ : LocalFieldData F).isOpen_ker_determinantComplexPower (m i + 1) _)
      (determinantComplexPower_upperUnipotent F (m i + 1) _)).mpr (hσ i)
  exact lowerInduced_inverseWhittakerType F h ψ (complexOppositeTwistBlocks F m σ u) hu

/-- A real-ray clearing assertion for every actual nonzero-functional
coefficient in the opposite-twist family, with fixed block polynomials. -/
def EqualOppositeRealRayClearing
    (μ : Measure (LeftUnipotentQuotient t F))
    (lambda : glFunctionals ψ t π) (P₀ P₁ : Polynomial ℂ) (C : ℝ) : Prop :=
  ∀ u : ℝ, C < u →
    ∀ ell : glInverseFunctionals ψ t (complexOppositeTwistInduced F m h σ (u : ℂ)),
      ell.val ≠ 0 →
    ∀ (f : (coefficientModel π lambda).toSubmodule)
      (f' : (coefficientModel (complexOppositeTwistInduced F m h σ (u : ℂ)) ell).toSubmodule)
      (Φ : SchwartzBruhat (Fin (t + 1) → F)),
    let a : BilateralLaurentSeries :=
      equalRankSliceCoefficient (⟨⟩ : LocalFieldData F) μ ψ f.val f'.val Φ
    ∃ L : LaurentPolynomial ℂ, ofLaurentPolynomial L =
      oppositeSpectralClearingKernel qF P₀ P₁ (u : ℂ) • a

/-- The large-twist symmetric bound, complete unramified transport and
uniqueness of normalized L polynomials give actual formal real-ray clearing. -/
theorem exists_equalOppositeRealRayClearing
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    [Measure.IsMulRightInvariant (unipotentHaar F t)]
    (μ : Measure (LeftUnipotentQuotient t F))
    (hμ : IsCompatible (upperUnipotent (t + 1) F)
      (generalLinearHaar F t) (unipotentHaar F t) μ)
    (lambda : glFunctionals ψ t π) (hlambda : lambda.val ≠ 0)
    (P₀ P₁ : Polynomial ℂ)
    (hP₀ : IsPadicSymmetricLPolynomial F ψ ν.val π (σ 0) P₀)
    (hP₁ : IsPadicSymmetricLPolynomial F ψ ν.val π (σ 1) P₁) :
    ∃ C : ℝ, EqualOppositeRealRayClearing F h ψ π σ μ lambda P₀ P₁ C := by
  obtain ⟨Cbound, hC⟩ := exists_equalTwoBlockSymmetricLBound F h ψ ν π hπ σ hσ
  refine ⟨Cbound, fun u hu ell hell f f' Φ => ?_⟩
  obtain ⟨P, Q₀, Q₁, hP, hQ₀, hQ₁, hdiv⟩ := hC u hu
  have hQ₀' := Langlands.AllField.RankinSelberg.Padic.symmetricLPolynomial_determinantComplexPower
    F ψ ν π (σ 0) (-(u : ℂ)) P₀ hP₀
  have hQ₁' := Langlands.AllField.RankinSelberg.Padic.symmetricLPolynomial_determinantComplexPower
    F ψ ν π (σ 1) (u : ℂ) P₁ hP₁
  have he0 : Q₀ = P₀.comp (C (spectralPoint qF (-(u : ℂ))) * X) := hQ₀.unique hQ₀'
  have he1 : Q₁ = P₁.comp (C (spectralPoint qF (u : ℂ)) * X) := hQ₁.unique hQ₁'
  rw [he0, he1] at hdiv
  let A := P₀.comp (C (spectralPoint qF (-(u : ℂ))) * X) *
    P₁.comp (C (spectralPoint qF (u : ℂ)) * X)
  have hA : A ≠ 0 := by
    have hc : A.coeff 0 = 1 := by
      simp [A, Polynomial.mul_coeff_zero, Polynomial.comp_C_mul_X_coeff,
        hP₀.coeff_zero, hP₁.coeff_zero]
    intro hz
    simp [hz] at hc
  exact equalRankCoefficient_clearing_of_certificate F ψ μ hμ π
    (complexOppositeTwistInduced F m h σ (u : ℂ)) hπ
    (complexOppositeTwistInduced_inverseWhittakerType F h ψ σ hσ (u : ℂ))
    lambda ell hlambda hell f f' Φ ν P A hA hP hdiv

/-- Continue the large-real-twist denominator bound to the original pair,
using actual entire determinant slices and the original ordered blocks. -/
theorem equalTwoBlockSymmetricLBound_at_zero
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) :
    EqualTwoBlockSymmetricLBound F h ψ ν π σ := by
  let := unipotentHaar_isMulRightInvariant F t
  let μ := unipotentQuotientHaar F t
  have hμ := unipotentQuotientHaar_isCompatible F t
  have hIndInv := lowerInduced_inverseWhittakerType F h ψ σ hσ
  have hInd := (isOfWhittakerType_standard_iff_inverse ψ _).mpr hIndInv
  obtain ⟨lambda, hlambda⟩ := hπ.exists_ne_zero
  obtain ⟨ell, hell⟩ := hIndInv.exists_ne_zero
  obtain ⟨P, hP⟩ := symmetricLPolynomialExists F ψ ν t t V
    (Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σ) π (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) hπ hInd
  obtain ⟨P₀, hP₀⟩ := symmetricLPolynomialExists F ψ ν t (m 0) V
    (W 0) π (σ 0) hπ (hσ 0)
  obtain ⟨P₁, hP₁⟩ := symmetricLPolynomialExists F ψ ν t (m 1) V
    (W 1) π (σ 1) hπ (hσ 1)
  obtain ⟨Cbound, hbound⟩ := exists_equalOppositeRealRayClearing F h ψ ν π σ
    hπ hσ μ hμ lambda hlambda P₀ P₁ hP₀ hP₁
  have hclear : EqualModelFiniteClearing F ψ μ π (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ)
      lambda ell (P₀ * P₁) := by
    intro f f' Φ
    obtain ⟨U, hU0, hcoeff, ⟨K, hKo, -, hK⟩, hUa⟩ :=
      exists_oppositeWhittakerFamily F m h σ ψ hσ ell hell f'
    have hae := (equalRankEntireSliceData F ψ μ π lambda f Φ U hπ.1.1
      K hKo hK hUa).2
    let a : ℂ → BilateralLaurentSeries := fun u =>
      equalRankSliceCoefficient (⟨⟩ : LocalFieldData F) μ ψ f.val (U u) Φ
    have hreal : ∀ u : ℝ, Cbound < u → ∃ L : LaurentPolynomial ℂ,
        ofLaurentPolynomial L = oppositeSpectralClearingKernel qF P₀ P₁ (u : ℂ) •
          a (u : ℂ) := by
      intro u hu
      obtain ⟨ellU, hellU, v, hv⟩ := hcoeff (u : ℂ)
      have hfU : (modelMap _ ellU v).val = U (u : ℂ) := hv
      obtain ⟨L, hL⟩ := hbound u hu ellU hellU f (modelMap _ ellU v) Φ
      rw [hfU] at hL
      exact ⟨L, hL⟩
    obtain ⟨L, hL⟩ := oppositeSpectralKernel_laurent_clearing_at_zero
      (⟨⟩ : LocalFieldData F).residueCardinality_gt_one P₀ P₁ a hae Cbound hreal
    exact ⟨L, by simpa only [a, hU0] using hL⟩
  have hA : P₀ * P₁ ≠ 0 := by
    have hc : (P₀ * P₁).coeff 0 = 1 := by
      rw [Polynomial.mul_coeff_zero, hP₀.coeff_zero, hP₁.coeff_zero, one_mul]
    intro hz
    simp [hz] at hc
  have hPμ := isPairLPolynomial_self.mp
    (((isPadicSymmetricLPolynomial_of_le (le_refl t)).mp hP).2 μ hμ)
  exact ⟨P, P₀, P₁, hP, hP₀, hP₁,
    equalModelFiniteClearing_polynomialDivisibility F ψ μ π
      (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) lambda ell hπ hIndInv hlambda hell
      P (P₀ * P₁) hA hPμ hclear⟩

end Blocks

end Langlands.AllField.RankinSelberg.DominantRankTransport
