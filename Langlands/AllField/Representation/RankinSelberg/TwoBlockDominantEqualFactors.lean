import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualFactors
import Langlands.AllField.Representation.RankinSelberg.SymmetricGammaExpressionProof
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantEqualRational
import Langlands.AllField.Representation.RankinSelberg.WhittakerTypeGammaConstructionInputProof
/-! # Identify retained block witnesses with symmetric factors -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg.DominantRankTransport hiding EqualFirstBlockCoefficientLaw EqualFirstBlockFactorCertificate EqualFirstBlockSymmetricFactors EqualLowerFourierCoefficientLaw EqualModelFiniteClearing EqualTwoBlockFiniteNumerators EqualTwoBlockRationalComparison EqualTwoBlockSymmetricLBound EqualTwoSidedFirstBlockLaws StrictModelFiniteClearing coe_equalResidueCardinalityUnit coefficientContinuationMatrixMeasurable coefficientContinuationQuotientMeasurable coefficientContinuationTopology determinantComplexPower_inverseTranspose determinantComplexPower_weylLong dualJacquetLocalField dualJacquetTopology dualJacquetValuation equalDualityBorel equalDualityGLBorel equalDualityGLMeasurable equalDualityLocalField equalDualityLowerBorel equalDualityLowerMeasurable equalDualityMeasurable equalDualityQuotientMeasurable equalDualityTopology equalDualityUnipotentBorel equalDualityUnipotentMeasurable equalDualityValuation equalFactorsGLBorel equalFactorsGLMeasurable equalFactorsLocalField equalFactorsMeasurable equalFactorsQuotientBorel equalFactorsQuotientMeasurable equalFactorsTopology equalFactorsUnipotentBorel equalFactorsUnipotentMeasurable equalFactorsValuation equalFirstBlockBorel equalFirstBlockGLBorel equalFirstBlockGLMeasurable equalFirstBlockLocalField equalFirstBlockLowerMeasurable equalFirstBlockLowerSeries equalFirstBlockMeasurable equalFirstBlockQuotientMeasurable equalFirstBlockSecondCountable equalFirstBlockTopology equalFirstBlockUnipotentBorel equalFirstBlockUnipotentMeasurable equalFirstBlockValuation equalLowerFourierCoefficientLaw equalLowerGroupIntegrand_reversedDual equalLowerIntegrand_reversedDual equalModelFiniteClearing_polynomialDivisibility equalNumeratorGLBorel equalNumeratorGLMeasurable equalNumeratorLocalField equalNumeratorQuotientMeasurable equalNumeratorTopology equalNumeratorUnipotentBorel equalNumeratorUnipotentMeasurable equalNumeratorValuation equalRank_hasBilateralSpectralExpansion equalRationalGLBorel equalRationalGLMeasurable equalRationalLocalField equalRationalQuotientMeasurable equalRationalTopology equalRationalUnipotentBorel equalRationalUnipotentMeasurable equalRationalValuation equalResidueCardinalityUnit equalSecondBlockBorel equalSecondBlockGLBorel equalSecondBlockGLMeasurable equalSecondBlockLocalField equalSecondBlockMeasurable equalSecondBlockQuotientMeasurable equalSecondBlockSecondCountable equalSecondBlockTopology equalSecondBlockUnipotentBorel equalSecondBlockUnipotentMeasurable equalSecondBlockValuation equalTwoBlockFiniteNumerators_of_laws equalTwoBlockRationalComparison_of_numerators equalTwoBlockSymmetricLBound_of_rationalComparison exists_equalFirstBlockBound_forOrdinaryFunctional exists_equalFirstBlockCoefficientLaw exists_equalTwoBlockFiniteNumerators exists_equalTwoBlockRationalComparison exists_equalTwoBlockSymmetricLBound exists_equalTwoSidedFirstBlockLaws exists_reversedEqualFirstBlockBound instBorelSpaceCarrier instMeasurableSpaceCarrier instTopologicalSpaceCarrier lowerInduced_inverseWhittakerType negatedSelfDualHaar negatedSelfDualHaar_val radicalAverage_eq_equalRankIntegrand reversedDualBlocks_whittakerType reversedDualSectionEquiv_ordinary reversedDual_oppositeTwistBlocks secondDual_oppositeTwistFunctional_val strictModelFiniteClearing_polynomialDivisibility symmetricFactors_of_modelCertificates symmetricLPolynomial_of_modelGenerator unequalRank_hasBilateralSpectralExpansion unfoldedJacquetSeries unfoldedJacquetSeries_eq
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
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding blockRotation_inv_mem_integralOpen blockRotation_inv_mul_mem_integralOpen blockRotation_mem_integralOpen canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance equalFactorsT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance equalFactorsMeasurable : MeasurableSpace F := borel _
local instance equalFactorsBorel : BorelSpace F := ⟨rfl⟩
local instance equalFactorsGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance equalFactorsGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance equalFactorsUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance equalFactorsUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
local instance equalFactorsQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F) := borel _
local instance equalFactorsQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩

local notation "qF" => (Langlands.LocalFieldData.residueCardinality (⟨⟩ : LocalFieldData F))
local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

section Identification

variable (ψ : UnitaryAdditiveCharacter F)
  (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
  {r n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {U : Type uW} [AddCommGroup U] [Module ℂ U]
  (π : Representation ℂ (GeneralLinear (r + 1) F) V)
  (σ : Representation ℂ (GeneralLinear (n + 1) F) U)
  (lambda : glFunctionals ψ r π) (ell : glInverseFunctionals ψ n σ)
  (μ : Measure (LeftUnipotentQuotient n F))

set_option maxHeartbeats 800000 in
/-- A model generator at one complementary rectangle determines the full
symmetric L certificate, including every compatible quotient measure. -/
theorem symmetricLPolynomial_of_modelGenerator
    (hnr : n < r)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ)
    (hlambda : lambda.val ≠ 0) (hell : ell.val ≠ 0)
    (hμ : IsCompatible (upperUnipotent (n + 1) F)
      (generalLinearHaar F n) (unipotentHaar F n) μ)
    (j k : ℕ) (hr : r = n + (j + k + 1)) {P : Polynomial ℂ}
    (hP : IsNormalizedGenerator
      (unequalRankValuesAt j k hr qF ψ abv μ
        (rectangularMeasure ν.val j (n + 1)) π σ lambda ell) P) :
    IsPadicSymmetricLPolynomial F ψ ν.val π σ P := by
  have hσinv := (isOfWhittakerType_standard_iff_inverse ψ σ).mp hσ
  have hA : UnequalRankAnalyticAt j k hr qF ψ abv μ
      (rectangularMeasure ν.val j (n + 1)) π σ lambda ell := by
    subst r
    exact unequalRankAnalytic F (⟨⟩ : LocalFieldData F) n j k ψ μ hμ ν.val
      V U π σ hπ hσinv lambda ell hlambda hell
  obtain ⟨P₀, hP₀⟩ := symmetricLPolynomialExists F ψ ν r n V U π σ hπ hσ
  have hP₀intrinsic := ((isPairLPolynomial_of_lt hnr).mp
    (((isPadicSymmetricLPolynomial_of_le hnr.le).mp hP₀).2 μ hμ)) j k hr
  have hEq : P = P₀ := hP.unique
    ((UnequalRankAnalyticAt.isNormalizedGenerator_iff j k hr hA
      hπ hσinv hlambda hell P₀).mp hP₀intrinsic)
  rw [hEq]
  exact hP₀

set_option maxHeartbeats 800000 in
/-- A fixed epsilon equation and its actual original and dual model generators
are the symmetric epsilon, L and gamma certificates for the same witnesses. -/
theorem symmetricFactors_of_modelCertificates
    (hnr : n < r)
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ)
    (hlambda : lambda.val ≠ 0) (hell : ell.val ≠ 0)
    (hμ : IsCompatible (upperUnipotent (n + 1) F)
      (generalLinearHaar F n) (unipotentHaar F n) μ)
    {c : ℂˣ} {d : ℤ} {P Pdual : Polynomial ℂ}
    (hFE : UnequalRankEpsilonEquation hnr qF ψ abv μ ν.val π σ lambda ell c d)
    (hgen : ∀ (j k : ℕ) (hr : r = n + (j + k + 1)),
      IsNormalizedGenerator
        (unequalRankValuesAt j k hr qF ψ abv μ
          (rectangularMeasure ν.val j (n + 1)) π σ lambda ell) P ∧
      IsNormalizedGenerator
        (dualUnequalRankRationalValuesAt hnr j k hr qF ψ abv μ ν.val
          π σ lambda ell) Pdual) :
    IsPadicSymmetricEpsilonFactor F ψ ν.val π σ (c, d) ∧
    IsPadicSymmetricLPolynomial F ψ ν.val π σ P ∧
    IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν.val
      (inverseTransposePullback π) (inverseTransposePullback σ) Pdual ∧
    IsPadicSymmetricGammaFactor F ψ ν.val π σ
      (rationalGammaExpression (Langlands.AllField.LocalFactor.residueReflection F) c d P Pdual) := by
  have hr : r = n + (0 + (r - n - 1) + 1) := by omega
  have hP := symmetricLPolynomial_of_modelGenerator F ψ ν π σ lambda ell μ
    hnr hπ hσ hlambda hell hμ 0 (r - n - 1) hr (hgen _ _ hr).1
  have hσinv := (isOfWhittakerType_standard_iff_inverse ψ σ).mp hσ
  have hπD := isOfWhittakerType_firstDual ψ π hπ
  have hσDinv := isOfWhittakerType_secondDual ψ σ hσinv
  have hσD := (isOfWhittakerType_standard_iff_inverse (ψ.scale (-1))
    (inverseTransposePullback σ)).mpr hσDinv
  have hdual := (hgen 0 (r - n - 1) hr).2
  rw [dualUnequalRankRationalValuesAt_eq] at hdual
  have hPd := symmetricLPolynomial_of_modelGenerator F (ψ.scale (-1))
    (negatedSelfDualHaar F ψ ν) (inverseTransposePullback π)
    (inverseTransposePullback σ) (firstDualFunctional ψ π lambda)
    (secondDualFunctional ψ σ ell) μ hnr hπD hσD
    (firstDualFunctional_ne_zero ψ π hlambda) (secondDualFunctional_ne_zero ψ σ hell)
    hμ (r - n - 1) 0 (by omega) hdual
  have he : IsPadicPairEpsilonFactor F ψ ν.val π σ (c, d) := by
    apply (isPairEpsilonFactor_of_lt hnr).mpr
    apply unequalRankEpsilonFactor_of_equation hnr hπ hσinv hlambda hell
    rwa [unipotentQuotientHaar_unique F n μ hμ] at hFE
  have hG := Langlands.AllField.RankinSelberg.IsPadicPairEpsilonFactor.gammaFactor_of_constructionInput F ψ ν.val π σ
    (padicPairGammaConstructionInput_of_whittakerType F ψ ν r n V U π σ hnr.le hπ hσinv)
    he ((isPadicSymmetricLPolynomial_of_le hnr.le).mp hP)
    ((isPadicSymmetricLPolynomial_of_le hnr.le).mp hPd)
  exact ⟨(isPadicSymmetricEpsilonFactor_of_le hnr.le).mpr he, hP, hPd,
    (isPadicSymmetricGammaFactor_of_le hnr.le).mpr hG⟩

end Identification

section Blocks

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

/-- The full symmetric certificates attached to the retained first-block
monomial and polynomial pair. -/
def EqualFirstBlockSymmetricFactors (c : ℂˣ) (d : ℤ)
    (P Pdual : Polynomial ℂ) : Prop :=
  IsPadicSymmetricEpsilonFactor F ψ ν.val π (σ 0) (c, d) ∧
  IsPadicSymmetricLPolynomial F ψ ν.val π (σ 0) P ∧
  IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν.val
    (inverseTransposePullback π) (inverseTransposePullback (σ 0)) Pdual ∧
  IsPadicSymmetricGammaFactor F ψ ν.val π (σ 0)
    (rationalGammaExpression (Langlands.AllField.LocalFactor.residueReflection F) c d P Pdual)

omit ell in
/-- No generator or epsilon data are replaced when a retained first-block
certificate is upgraded to symmetric factors. -/
theorem EqualFirstBlockFactorCertificate.symmetricFactors
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (hlambda : lambda.val ≠ 0)
    (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (hell : (ell 0).val ≠ 0)
    {μA : Measure (LeftUnipotentQuotient (m 0) F)}
    (hμA : IsCompatible (upperUnipotent (m 0 + 1) F)
      (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) μA)
    {ζ c : ℂˣ} {d : ℤ} {P Pdual : Polynomial ℂ}
    (hcert : EqualFirstBlockFactorCertificate F h ψ ν π lambda σ ell μA
      ζ c d P Pdual) :
    EqualFirstBlockSymmetricFactors F ψ ν π σ c d P Pdual :=
  symmetricFactors_of_modelCertificates F ψ ν π (σ 0) lambda (ell 0) μA
    (firstBlock_lt_total h) hπ (hσ 0) hlambda hell hμA hcert.1 hcert.2.2

/-- The actual equal-rank lower induction and both actual blocks have complete
symmetric L certificates with the required divisibility direction. -/
def EqualTwoBlockSymmetricLBound : Prop :=
  ∃ P P₁ P₂ : Polynomial ℂ,
    IsPadicSymmetricLPolynomial F ψ ν.val π (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) P ∧
    IsPadicSymmetricLPolynomial F ψ ν.val π (σ 0) P₁ ∧
    IsPadicSymmetricLPolynomial F ψ ν.val π (σ 1) P₂ ∧
    ∃ (Q : Polynomial ℂ) (e : ℕ), X ^ e * (P₁ * P₂) = Q * P

set_option maxHeartbeats 1600000 in
/-- Identify the retained first-block polynomials in both directions and apply
the intrinsic bound to a certified whole-pair L polynomial. -/
theorem equalTwoBlockSymmetricLBound_of_rationalComparison
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (hσtype : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (hlambda : lambda.val ≠ 0) (hell : ∀ i, (ell i).val ≠ 0)
    (hσ : ∀ i, IsSmooth (σ i))
    (J : glInverseFunctionals ψ t (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ))
    (μN : Measure (LeftUnipotentQuotient t F))
    (μA : Measure (LeftUnipotentQuotient (m 0) F))
    (μB : Measure (LeftUnipotentQuotient (m 1) F))
    (hμN : IsCompatible (upperUnipotent (t + 1) F)
      (generalLinearHaar F t) (unipotentHaar F t) μN)
    (hμA : IsCompatible (upperUnipotent (m 0 + 1) F)
      (generalLinearHaar F (m 0)) (unipotentHaar F (m 0)) μA)
    (hμB : IsCompatible (upperUnipotent (m 1 + 1) F)
      (generalLinearHaar F (m 1)) (unipotentHaar F (m 1)) μB)
    (hR : EqualTwoBlockRationalComparison F h ψ ν π lambda σ ell hσ J μN μA μB) :
    EqualTwoBlockSymmetricLBound F h ψ ν π σ := by
  obtain ⟨ζ₁, c₁, ζ₂, c₂, d₁, d₂, P₁, P₁D, P₂, P₂D,
    hcert₁, hcert₂, -, -, hbound⟩ := hR
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
  have hP₂ : IsPadicSymmetricLPolynomial F ψ ν.val π (σ 1) P₂ := by
    have hh := hsecond.2.2.1
    change IsPadicSymmetricLPolynomial F ((ψ.scale (-1)).scale (-1)) ν.val
      (inverseTransposePullback (inverseTransposePullback π))
      (inverseTransposePullback (inverseTransposePullback (σ 1))) P₂ at hh
    simpa only [UnitaryAdditiveCharacter.scale_scale, neg_one_mul, neg_neg,
      UnitaryAdditiveCharacter.scale_one, inverseTransposePullback_involutive] using hh
  have hIndInv := lowerInduced_inverseWhittakerType F h ψ σ hσtype
  have hInd := (isOfWhittakerType_standard_iff_inverse ψ
    (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ)).mpr hIndInv
  obtain ⟨P, hP⟩ := symmetricLPolynomialExists F ψ ν t t V
    (Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σ) π (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) hπ hInd
  have hPμ := ((isPadicSymmetricLPolynomial_of_le (le_refl t)).mp hP).2 μN hμN
  exact ⟨P, P₁, P₂, hP, hfirst.2.1, hP₂, hbound P (isPairLPolynomial_self.mp hPμ)⟩

omit lambda σ ell in
set_option maxHeartbeats 1600000 in
/-- Complete symmetric L certificates satisfy the required bound for all
sufficiently large real opposite twists of arbitrary Whittaker-type blocks.
No nonzero functional, measure compatibility or analytic identity is a premise. -/
theorem exists_equalTwoBlockSymmetricLBound
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i)) :
    ∃ Cbound : ℝ, ∀ u : ℝ, Cbound < u →
      EqualTwoBlockSymmetricLBound F h ψ ν π (twoBlockOppositeTwistBlocks F m τ u) := by
  let := unipotentHaar_isMulRightInvariant F t
  let := unipotentHaar_isMulRightInvariant F (m 0)
  let := unipotentHaar_isMulRightInvariant F (m 1)
  obtain ⟨lambda, hlambda⟩ := hπ.exists_ne_zero
  have hex : ∀ i, ∃ ell : glInverseFunctionals ψ (m i) (τ i), ell.val ≠ 0 :=
    fun i => ((isOfWhittakerType_standard_iff_inverse ψ (τ i)).mp (hτ i)).exists_ne_zero
  choose ell0 hell0 using hex
  obtain ⟨Cbound, hCbound⟩ := exists_equalTwoBlockRationalComparison F h ψ ν π lambda
    hπ hlambda τ hτ ell0 hell0
  refine ⟨Cbound, fun u hu => ?_⟩
  obtain ⟨-, Ju, -, -, hR⟩ := hCbound u hu
  let σu := twoBlockOppositeTwistBlocks F m τ u
  have hσu : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σu i) :=
    fun i => (twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u i _).mpr
      (hτ i)
  let μN := unipotentQuotientHaar F t
  let μA := unipotentQuotientHaar F (m 0)
  let μB := unipotentQuotientHaar F (m 1)
  have hμN := unipotentQuotientHaar_isCompatible F t
  have hμA := unipotentQuotientHaar_isCompatible F (m 0)
  have hμB := unipotentQuotientHaar_isCompatible F (m 1)
  exact equalTwoBlockSymmetricLBound_of_rationalComparison F h ψ ν π lambda σu
    (fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i))
    hπ hσu hlambda hell0 (fun i => (hσu i).1.1) Ju μN μA μB hμN hμA hμB
    (hR μN μA μB hμN hμA hμB)

end Blocks

end Langlands.AllField.RankinSelberg.DominantRankTransport
