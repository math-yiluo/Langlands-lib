import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualGammaComparison
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantCentralScalar
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantEqualFactors
noncomputable section

namespace Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg.DominantRankTransport hiding EqualFirstBlockCoefficientLaw EqualFirstBlockFactorCertificate EqualFirstBlockSymmetricFactors EqualLowerFourierCoefficientLaw EqualModelFiniteClearing EqualTwoBlockFiniteNumerators EqualTwoBlockRationalComparison EqualTwoBlockSymmetricGammaProduct EqualTwoBlockSymmetricLBound EqualTwoSidedFirstBlockLaws StrictModelFiniteClearing coe_equalResidueCardinalityUnit coefficientContinuationMatrixMeasurable coefficientContinuationQuotientMeasurable coefficientContinuationTopology determinantComplexPower_inverseTranspose determinantComplexPower_weylLong dualJacquetLocalField dualJacquetTopology dualJacquetValuation equalDualityBorel equalDualityGLBorel equalDualityGLMeasurable equalDualityLocalField equalDualityLowerBorel equalDualityLowerMeasurable equalDualityMeasurable equalDualityQuotientMeasurable equalDualityTopology equalDualityUnipotentBorel equalDualityUnipotentMeasurable equalDualityValuation equalFactorsGLBorel equalFactorsGLMeasurable equalFactorsLocalField equalFactorsMeasurable equalFactorsQuotientBorel equalFactorsQuotientMeasurable equalFactorsTopology equalFactorsUnipotentBorel equalFactorsUnipotentMeasurable equalFactorsValuation equalFirstBlockBorel equalFirstBlockGLBorel equalFirstBlockGLMeasurable equalFirstBlockLocalField equalFirstBlockLowerMeasurable equalFirstBlockLowerSeries equalFirstBlockMeasurable equalFirstBlockQuotientMeasurable equalFirstBlockSecondCountable equalFirstBlockTopology equalFirstBlockUnipotentBorel equalFirstBlockUnipotentMeasurable equalFirstBlockValuation equalGammaMeasurable equalGammaProductGLBorel equalGammaProductGLMeasurable equalGammaProductLocalField equalGammaProductMeasurable equalGammaProductQuotientMeasurable equalGammaProductTopology equalGammaProductUnipotentBorel equalGammaProductUnipotentMeasurable equalGammaProductValuation equalGammaTopology equalLowerFourierCoefficientLaw equalLowerGroupIntegrand_reversedDual equalLowerIntegrand_reversedDual equalModelFiniteClearing_polynomialDivisibility equalNumeratorGLBorel equalNumeratorGLMeasurable equalNumeratorLocalField equalNumeratorQuotientMeasurable equalNumeratorTopology equalNumeratorUnipotentBorel equalNumeratorUnipotentMeasurable equalNumeratorValuation equalRank_hasBilateralSpectralExpansion equalRationalGLBorel equalRationalGLMeasurable equalRationalLocalField equalRationalQuotientMeasurable equalRationalTopology equalRationalUnipotentBorel equalRationalUnipotentMeasurable equalRationalValuation equalResidueCardinalityUnit equalSecondBlockBorel equalSecondBlockGLBorel equalSecondBlockGLMeasurable equalSecondBlockLocalField equalSecondBlockMeasurable equalSecondBlockQuotientMeasurable equalSecondBlockSecondCountable equalSecondBlockTopology equalSecondBlockUnipotentBorel equalSecondBlockUnipotentMeasurable equalSecondBlockValuation equalTwoBlockFiniteNumerators_of_laws equalTwoBlockRationalComparison_of_numerators equalTwoBlockSymmetricGammaProduct_of_rationalComparison equalTwoBlockSymmetricLBound_of_rationalComparison exists_equalFirstBlockBound_forOrdinaryFunctional exists_equalFirstBlockCoefficientLaw exists_equalTwoBlockFiniteNumerators exists_equalTwoBlockRationalComparison exists_equalTwoBlockSymmetricLBound exists_equalTwoSidedFirstBlockLaws exists_reversedEqualFirstBlockBound hasModelMinusOneScalar_of_jacquetRealization instBorelSpaceCarrier instMeasurableSpaceCarrier instTopologicalSpaceCarrier jacquetFunction_blockMinusOne leviEmbedding_blockMinusOne leviModulus_blockMinusOne lowerInduced_inverseWhittakerType negatedSelfDualHaar negatedSelfDualHaar_val radicalAverage_eq_equalRankIntegrand reversedDualBlocks_whittakerType reversedDualSectionEquiv_ordinary reversedDual_oppositeTwistBlocks scalarSection_blockMinusOne secondDual_oppositeTwistFunctional_val strictModelFiniteClearing_polynomialDivisibility symmetricFactors_of_modelCertificates symmetricLPolynomial_of_modelGenerator tensorContraction_blockMinusOne unequalRank_hasBilateralSpectralExpansion unfoldedJacquetSeries unfoldedJacquetSeries_eq
open Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg hiding AdjacentRankBaseModelStarIdentity AdjacentRankModelConvergenceStatement AdjacentRankModelStarStatement CentralBilinearVanishingStatement CharacterChangeCompatibleMeasureStatement EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankContinuedFormsStatement EqualRankFactorSwapStatement EqualRankFrobeniusStatement EqualRankFunctionalEquationStatement EqualRankGammaExistenceStatement EqualRankLastRowReductionStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement EqualRankTrilinearMirabolicPrerequisites EqualRankTrilinearPrerequisites EqualRankTrilinearUniquenessStatement EqualRankUnitValueStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement LowerFirstBlockIntegrationInputStatement LowerFirstBlockSliceTowerInputStatement NormalizedProductWhittakerTypeStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RankOneCharacterReductionStatement RankOneGammaTwistStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement RootTorusProductStatement SliceIntegrable SliceIntegrableAt SymmetricLPolynomialExistenceStatement TwoBlockDualSectionJacquetStatement TwoBlockFirstBlockLaurentIdentityStatement TwoBlockFirstBlockQuotientIntegrationStatement TwoBlockFixedSliceUnfoldingStatement TwoBlockGammaAdjacentRankStatement TwoBlockGammaDominantRankStatement TwoBlockGammaRankOneStatement TwoBlockJacquetConvergenceStatement TwoBlockLAdjacentRankStatement TwoBlockLDominantRankStatement TwoBlockLRankOneStatement TwoBlockLowerFirstBlockQuotientIntegrationStatement TwoBlockLowerFixedSliceConvergenceStatement TwoBlockOrdinaryJacquetFunctionalStatement TwoBlockUnipotentQuotientIntegrationStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UniformFiniteFunctionMellinConvergenceStatement UnipotentCharacterChangeModulusStatement WhittakerRowSliceCompactSupportStatement WhittakerTypeGammaConstructionInputStatement ZeroRowLastRowCutoffStatement adjacentRankFullFourier adjacentRankFullFourier_inverseTranspose adjacentRankFullFourier_tmul adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelStar adjacentRankModelStarBase_of_pure_integrals adjacentRankModelStarIntegrabilityLocalInstance1 adjacentRankModelStarIntegrabilityLocalInstance2 adjacentRankModelStarIntegrabilityLocalInstance3 adjacentRankModelStarIntegrabilityLocalInstance4 adjacentRankModelStarIntegrabilityLocalInstance5 adjacentRankModelStarIntegrabilityLocalInstance6 adjacentRankModelStarIntegrabilityLocalInstance7 adjacentRankModelStarIntegrabilityLocalInstance8 adjacentRankModelStarIntegrabilityLocalInstance9 adjacentRankModelStarSourceFunction_regularity adjacentRankModelStarTargetFunction_regularity adjacentRankModelStar_base adjacentRankModelStar_equality_of_base adjacentRankModelStar_pure_right_averages adjacentRankPure_hasCompactSupport adjacentRankTransformedIntegrand adjacentRankTransformedPure_hasCompactSupport adjacentRankTransformed_integrable_of_isSmooth adjacentRank_distribHaarChar adjacentRank_fullFourier_kernel_reflected_orbit adjacentRank_fullFourier_rowTranslate adjacentRank_inverseTranspose_unipotent_epsilon adjacentRank_kernel_reflected_right_orbit adjacentRank_kernel_right_unipotent adjacentRank_partialFourier_rowTranslate adjacentRank_rho0_kernel_right_orbit assembleLowerFirstBlockQuotientIntegration centralBilinearVanishing centralSpectralElement centralSpectralElement_det_abs centralSpectralElement_mem_center characterChangeCompatibleMeasure characterChangeCompatibleMeasure_of_unipotentModulus continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice determinantWeight_centralSpectralElement diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankAnalytic equalRankCompactRootExpansion equalRankContinuedForms equalRankFactorSwap equalRankFrobenius equalRankFunctionalEquation equalRankGammaExistence equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankLastRowReduction equalRankNormalizedCompactIntegration equalRankQuotientAnalytic equalRankRootAverageAnalytic equalRankRootExpansion equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport equalRankTrilinearPrerequisites_of_mirabolic equalRankTrilinearUniqueness equalRankTrilinearUniqueness_of_mirabolic_prerequisites equalRankTrilinearUniqueness_of_prerequisites equalRankUnitValue exists_adjacentRank_lastColumn_bound exists_iwasawa_diagonal_le_of_simpleRoot exists_rankOneCutoff exists_rankOneEmbedding_support exists_schwartzBruhat_row_bound finiteFunctionMellin finiteFunctionShellSeries generalLinearDeterminantSlice hasCompactSupport_matrixSlice hasEqualRankCompactTest_of_kirillov hasSum_setIntegral_determinantSlice iUnion_determinantSlice inverseUniformizer_normalizedAbsoluteValue isClopen_determinantSlice isClopen_generalLinearDeterminantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOfWhittakerType_quasicharacter_twist_iff isOpen_determinantSlice isPadicPairEpsilonFactor_swap_equalRank isPadicPairGammaFactor_swap_equalRank isPadicPairLPolynomial_swap_equalRank isPadicPairLPolynomial_twist isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricGammaFactor_rankOne_test_twist isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt isPadicSymmetricLPolynomial_rankOne_test_twist isPadicSymmetricLPolynomial_twist iwasawaTorusSum lastRowCompactOrbit leviModulus_characterChangeLevi leviModulus_characterChangeLevi_eq_pow lowerFirstBlockIntegrationInput_of_sliceTower lowerFirstBlockSliceTowerInput matrixSliceTest matrixSliceTest_apply measurableSet_determinantSlice mem_determinantSlice mem_generalLinearDeterminantSlice mirabolic_exists_exception_length_le_one mirabolic_pair_control_of_statements mirabolic_shift_length_bound mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer modelStarBaseBorel modelStarBaseDisconnected modelStarBaseGLBorel modelStarBaseGLMeasurable modelStarBaseLocalField modelStarBaseMeasurable modelStarBaseT2 modelStarBaseTopology modelStarBaseUnipotentBorel modelStarBaseUnipotentMeasurable modelStarBaseValuative modelStarFourierBorel modelStarFourierDisconnected modelStarFourierLocalField modelStarFourierMeasurable modelStarFourierT2 modelStarFourierTopology modelStarFourierValuative modelStarOrbitFourierBorel modelStarOrbitFourierDisconnected modelStarOrbitFourierLocalField modelStarOrbitFourierMeasurable modelStarOrbitFourierSecondCountable modelStarOrbitFourierT2 modelStarOrbitFourierTopology modelStarOrbitFourierValuative modelStarReductionBorel modelStarReductionDisconnected modelStarReductionGLBorel modelStarReductionGLMeasurable modelStarReductionLocalField modelStarReductionMeasurable modelStarReductionT2 modelStarReductionTopology modelStarReductionValuative modelStarRegularityLocalField modelStarRegularityTopology modelStarRegularityValuative normalizedAbs_det_of_mem_generalLinearDeterminantSlice normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow normalizedProductWhittakerType oneVariableMellin padicPairGammaConstructionInput_iff padicPairGammaConstructionInput_of_whittakerType padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType padic_quotient_sigmaFinite padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice quasicharacterSmoothCharacter quasicharacter_isOpen_ker quotientHaarExistence quotientIwasawaIntegration quotientRootIntegration rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneGammaTwist rankOneMatrixWhittakerComparison rankOneMatrixWhittakerComparison_of_positive rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct setIntegral_equalRankIntegrand_determinantSlice setIntegral_unequalRankAverage_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrableAt_unequalRankAverage_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice symmetricLPolynomialExists twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockDualSectionJacquet twoBlockFirstBlockLaurentIdentity twoBlockFirstBlockQuotientIntegration twoBlockFixedSliceUnfolding twoBlockGammaRankOne_of_trivial_test twoBlockJacquetConvergence twoBlockLRankOne_of_trivial_test twoBlockLowerFirstBlockQuotientIntegration twoBlockLowerFixedSliceConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val twoBlockOrdinaryJacquetFunctional twoBlockUnipotentQuotientIntegration unequalRankAnalytic unequalRankAverage unequalRankAverage_eq_mul_spectralPoint_zpow unequalRankCommonGenerator unequalRankCompactSupport unequalRankFiniteExpansion unequalRankFunctionalEquation unequalRankGammaPropagation unequalRankIntegrand_eq_mul_spectralPoint_zpow unequalRankIwasawaSupport unequalRankSliceCoefficient unequalRankSliceExpansion unequalRankSliceExpansion_of_converges unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unequalSliceMatrixMeasurable unequalSliceQuotientBorel unequalSliceQuotientMeasurable unequalSliceTopology unipotentCharacterChangeModulus unipotentHaar_mul_diagonal_le unipotentVolumeLocalField unipotentVolumeTopology unipotentVolumeValuativeRel whittakerRationalValues_eq_rankOneModelValues whittakerRowSliceCompactSupport whittakerTypeGammaConstructionInput zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Polynomial
open Langlands.HarmonicAnalysis hiding AdjacentRankUnipotentFourierStatement PadicMatrixFourierSliceStatement PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement TwoBlockRowFourierCompanionStatement adjacentRankUnipotentFourier exists_rowSchwartz_order_lower_bound padicLatticeGeometry padicMatrixFourierSlice padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists padicUnipotentHaar_iota_fourier_duality_right twoBlockRowFourierCompanion
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding CompactLocalizationStatement MirabolicCompactTwistedPairingStatement MirabolicFiniteLengthStatement MirabolicFunctionalMultiplicityStatement MirabolicTwistedPairingRigidityStatement MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier UnipotentOrbitStatement compactLocalization exchangedParabolic exists_compactOpen_glCoefficientRightStabilizer functionalsCongr hasCompactSupport_twoBlockCellRestriction inducedLocalization_of_prerequisites mirabolicCompactTwistedPairing mirabolicFiniteLength mirabolicFunctionalMultiplicity mirabolicTwistedPairingRigidity mirabolicUnitTest modelKirillovTransfer mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentOrbit unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.LocalFactor hiding coe_residueReflection residueReflection
open Langlands.AllField.LocalFactor
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding blockRotation_inv_mem_integralOpen blockRotation_inv_mul_mem_integralOpen blockRotation_mem_integralOpen canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open scoped NNReal

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance equalGammaProductT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance equalGammaProductMeasurable : MeasurableSpace F := borel _
local instance equalGammaProductBorel : BorelSpace F := ⟨rfl⟩
local instance equalGammaProductGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance equalGammaProductGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance equalGammaProductUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance equalGammaProductUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
local instance equalGammaProductQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F) := borel _
local instance equalGammaProductQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩

local notation "qF" => (Langlands.LocalFieldData.residueCardinality (⟨⟩ : LocalFieldData F))
local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
  [hmod : ∀ i, Module ℂ (W i)]

variable (ψ : UnitaryAdditiveCharacter F)
  (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (t + 1) F) V)
  (lambda : glFunctionals ψ t π)
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
  (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))

/-- Complete gamma certificates for the two original blocks and their product
for the actual ordinary lower induction. -/
def EqualTwoBlockSymmetricGammaProduct : Prop :=
  ∃ G₁ G₂ : RationalFunctions,
    IsPadicSymmetricGammaFactor F ψ ν.val π (σ 0) G₁ ∧
    IsPadicSymmetricGammaFactor F ψ ν.val π (σ 1) G₂ ∧
    IsPadicSymmetricGammaFactor F ψ ν.val π (inducedRep F h σ) (G₁ * G₂)

set_option maxHeartbeats 1600000 in
/-- The retained actual rational comparison identifies a certified induced
factor with the product of complete certified block factors. -/
theorem equalTwoBlockSymmetricGammaProduct_of_rationalComparison
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (hσtype : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (hlambda : lambda.val ≠ 0) (hell : ∀ i, (ell i).val ≠ 0)
    (hσ : ∀ i, IsSmooth (σ i))
    (J : glInverseFunctionals ψ t (inducedRep F h σ))
    (hJ0 : J.val ≠ 0)
    (hJ : ∀ (f : Sections F h σ) (g : GeneralLinear (t + 1) F),
      J.val (inducedRep F h σ g f) =
        jacquetFunction ψ (fun i => (ell i).val)
          (rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)) f g)
    (μN : Measure (LeftUnipotentQuotient t F))
    (μA : Measure (LeftUnipotentQuotient (m 0) F))
    (μB : Measure (LeftUnipotentQuotient (m 1) F))
    (hμN : IsCompatible (upperUnipotent (t + 1) F)
      (generalLinearHaar F t) (unipotentHaar F t) μN)
    (hμA : IsCompatible (upperUnipotent (m 0 + 1) F)
      (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) μA)
    (hμB : IsCompatible (upperUnipotent (m 1 + 1) F)
      (generalLinearHaar F (m 1)) (unipotentHaar F (m 1)) μB)
    (hRational : EqualTwoBlockRationalComparison F h ψ ν π lambda σ ell hσ J μN μA μB) :
    EqualTwoBlockSymmetricGammaProduct F h ψ ν π σ := by
  let := unipotentHaar_isMulRightInvariant F t
  let := unipotentHaar_isMulRightInvariant F (m 0)
  let := unipotentHaar_isMulRightInvariant F (m 1)
  let q := equalResidueCardinalityUnit F
  have hq := (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
  have hδ : (q⁻¹ : ℂˣ) = Langlands.AllField.LocalFactor.residueReflection F := by
    apply Units.ext
    simp only [Units.val_inv_eq_inv_val, q, coe_equalResidueCardinalityUnit,
      Langlands.AllField.LocalFactor.coe_residueReflection]
  have hδval : (↑(q⁻¹) : ℂ) = (qF : ℂ)⁻¹ := by
    simp only [Units.val_inv_eq_inv_val, q, coe_equalResidueCardinalityUnit]
  obtain ⟨ζ₁, c₁, ζ₂, c₂, d₁, d₂, P₁, P₁D, P₂, P₂D,
    hcert₁, hcert₂, hcompare, -, -⟩ := hRational
  have hfirst := Langlands.AllField.RankinSelberg.DominantRankTransport.EqualFirstBlockFactorCertificate.symmetricFactors F h ψ ν π lambda σ
    hπ hσtype hlambda ell (hell 0) hμA hcert₁
  have hπD := isOfWhittakerType_firstDual ψ π hπ
  have hσD := reversedDualBlocks_whittakerType F σ ψ hσtype
  have hsecond := Langlands.AllField.RankinSelberg.DominantRankTransport.EqualFirstBlockFactorCertificate.symmetricFactors F (reverse_sum h)
    (ψ.scale (-1)) (negatedSelfDualHaar F ψ ν) (inverseTransposePullback π)
    (firstDualFunctional ψ π lambda)
    (fun i : Fin 2 => inverseTransposePullback (σ i.rev)) hπD hσD
    (firstDualFunctional_ne_zero ψ π hlambda)
    (fun i : Fin 2 => secondDualFunctional ψ (σ i.rev) (ell i.rev))
    (secondDualFunctional_ne_zero ψ (σ (0 : Fin 2).rev) (hell (0 : Fin 2).rev))
    hμB hcert₂
  have hG₁ : IsPadicSymmetricGammaFactor F ψ ν.val π (σ 0)
      (rationalGammaExpression q⁻¹ c₁ d₁ P₁ P₁D) := by
    rw [hδ]
    exact hfirst.2.2.2
  have hGD₂ : IsPadicSymmetricGammaFactor F (ψ.scale (-1)) ν.val
      (inverseTransposePullback π) (inverseTransposePullback (σ 1))
      (rationalGammaExpression q⁻¹ c₂ d₂ P₂D P₂) := by
    rw [hδ]
    exact hsecond.2.2.2
  have hsum : (m 0 + 1) + (m 1 + 1) = t + 1 := by
    simpa only [Fin.sum_univ_two] using h
  have hm₁ : m 1 < t := by omega
  let g₂ := padicSymmetricGammaFactorOfWhittakerType F ψ ν.val π (σ 1)
    (whittakerTypeGammaConstructionInput F ψ ν t (m 1) V (W 1)
      π (σ 1) hπ (hσtype 1))
  have hG₂Eq := ((isPairGammaFactor_of_lt hm₁).mp
    ((isPadicSymmetricGammaFactor_of_le hm₁.le).mp g₂.property)).2.2.2
      μB hμB lambda (ell 1) hlambda (hell 1)
  have hGD₂Eq := ((isPairGammaFactor_of_lt hm₁).mp
    ((isPadicSymmetricGammaFactor_of_le hm₁.le).mp hGD₂)).2.2.2
      μB hμB (firstDualFunctional ψ π lambda) (secondDualFunctional ψ (σ 1) (ell 1))
      (firstDualFunctional_ne_zero ψ π hlambda)
      (secondDualFunctional_ne_zero ψ (σ 1) (hell 1))
  have hrec := unequalRankGammaEquation_reflection_mul hq hδval (hell 1) hG₂Eq hGD₂Eq
  obtain ⟨η₂, hη₂⟩ := exists_modelMinusOneScalar (σ 1)
    ((isOfWhittakerType_standard_iff_inverse ψ (σ 1)).mp (hσtype 1))
  have hη₂D := hasModelMinusOneScalar_secondDual ψ (σ 1) (ell 1) (hη₂ (ell 1))
  have hη₂eq : η₂ = ζ₂ := hη₂D.unique
    (secondDualFunctional_ne_zero ψ (σ 1) (hell 1)) hcert₂.2.1
  have hζ₂ : HasModelMinusOneScalar (σ 1) (ell 1) ζ₂ := by
    rw [← hη₂eq]
    exact hη₂ (ell 1)
  let ζblocks : Fin 2 → ℂˣ := ![ζ₁, ζ₂]
  have hζblocks : ∀ i, HasModelMinusOneScalar (σ i) (ell i) (ζblocks i) := by
    intro i
    fin_cases i
    · exact hcert₁.2.1
    · exact hζ₂
  have hζInd : HasModelMinusOneScalar (inducedRep F h σ) J (ζ₁ * ζ₂) := by
    simpa only [Fin.prod_univ_two, ζblocks, Matrix.cons_val_zero, Matrix.cons_val_one]
      using hasModelMinusOneScalar_of_jacquetRealization F h ψ σ ell ζblocks hζblocks
        (rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)) J hJ
  have hP₁D : P₁D ≠ 0 :=
    (hcert₁.2.2 0 (m 1) (by omega)).2.polynomial_ne_zero
  have hP₂ : P₂ ≠ 0 :=
    (hcert₂.2.2 0 (m 0) (by change t = m 1 + (0 + m 0 + 1); omega)).2.polynomial_ne_zero
  have hP₂D : P₂D ≠ 0 :=
    (hcert₂.2.2 0 (m 0) (by change t = m 1 + (0 + m 0 + 1); omega)).1.polynomial_ne_zero
  have hIndInv := lowerInduced_inverseWhittakerType F h ψ σ hσtype
  have hInd := (isOfWhittakerType_standard_iff_inverse ψ (inducedRep F h σ)).mpr hIndInv
  let g := padicSymmetricGammaFactorOfWhittakerType F ψ ν.val π (inducedRep F h σ)
    (whittakerTypeGammaConstructionInput F ψ ν t t V (Sections F h σ)
      π (inducedRep F h σ) hπ hInd)
  have hEq := (isPairGammaFactor_self.mp
    ((isPadicSymmetricGammaFactor_of_le (le_refl t)).mp g.property)).2.2.2
      μN hμN lambda J hlambda hJ0
  obtain ⟨ζ, hζ, ⟨R₀, ⟨U, U', Φ, hR₀⟩, hR₀0⟩, hFE⟩ := hEq
  obtain ⟨f, rfl⟩ := modelMap_surjective (inducedRep F h σ) J U'
  obtain ⟨Φhat, R₁, RD₁, hpair, hR₁, hRD₁, hGamma⟩ :=
    hFE U (modelMap (inducedRep F h σ) J f) Φ
  obtain ⟨R₂, RD₂, hR₂, hRD₂, hclear⟩ := hcompare f U Φ Φhat hpair
  have hRD₂' : HasRationalContinuation qF
      (dualEqualRankModelIntegral ψ abv μN π (inducedRep F h σ) lambda J U
        (modelMap (inducedRep F h σ) J f) Φhat) RD₂ := by
    rw [transportedSecondDualFunctional_coefficient] at hRD₂
    exact hRD₂
  have hR₁₂ : R₁ = R₂ := hR₁.unique hq hR₂
  have hRD₁₂ : RD₁ = RD₂ := hRD₁.unique hq hRD₂'
  have hR₂0 : R₂ ≠ 0 := by rwa [← hR₀.unique hq hR₂]
  have hζeq : ζ = ζ₁ * ζ₂ := hζ.unique hJ0 hζInd
  have hactual := (RationalGammaComparison.gammaFunctionalEquation_iff_rational_identity
    hq hδval).mp hGamma
  rw [hR₁₂, hRD₁₂, hζeq] at hactual
  have hproduct := reflectedComparison_gammaProduct q ζ₁ c₁ d₁ ζ₂ c₂ d₂ t
    (hζ₂.sq_eq_one (hell 1)) hP₁D hP₂ hP₂D hrec hclear
  have hC : RatFunc.C (((ζ₁ * ζ₂ : ℂˣ) : ℂ) ^ t) ≠ 0 :=
    (_root_.map_ne_zero RatFunc.C).mpr (pow_ne_zero t (ζ₁ * ζ₂).ne_zero)
  have hg : (g.val : RationalFunctions) =
      rationalGammaExpression q⁻¹ c₁ d₁ P₁ P₁D * (g₂.val : RationalFunctions) :=
    mul_right_cancel₀ hR₂0 (mul_left_cancel₀ hC (hactual.symm.trans hproduct))
  exact ⟨_, _, hG₁, g₂.property, by rw [← hg]; exact g.property⟩

end Langlands.AllField.RankinSelberg.DominantRankTransport
