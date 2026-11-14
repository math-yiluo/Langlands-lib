import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualGammaFamilies
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantEqualLContinuation
noncomputable section

namespace Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg.DominantRankTransport hiding EqualFirstBlockCoefficientLaw EqualFirstBlockFactorCertificate EqualFirstBlockSymmetricFactors EqualLowerFourierCoefficientLaw EqualModelFiniteClearing EqualOppositeRealRayClearing EqualRankEntireSliceData EqualTwoBlockFiniteNumerators EqualTwoBlockRationalComparison EqualTwoBlockSymmetricLBound EqualTwoSidedFirstBlockLaws OppositeWhittakerFamilyData StrictModelFiniteClearing ambient_mul_firstBlock_eq_opposite coe_equalResidueCardinalityUnit coefficientContinuationMatrixMeasurable coefficientContinuationQuotientMeasurable coefficientContinuationTopology complexOppositeTwistBlocks complexOppositeTwistInduced complexOppositeTwistInduced_inverseWhittakerType determinantComplexPower_inverseTranspose determinantComplexPower_weylLong dualJacquetLocalField dualJacquetTopology dualJacquetValuation equalDualityBorel equalDualityGLBorel equalDualityGLMeasurable equalDualityLocalField equalDualityLowerBorel equalDualityLowerMeasurable equalDualityMeasurable equalDualityQuotientMeasurable equalDualityTopology equalDualityUnipotentBorel equalDualityUnipotentMeasurable equalDualityValuation equalEntireLocalField equalEntireQuotientBorel equalEntireQuotientMeasurable equalEntireTopology equalEntireValuation equalFactorsGLBorel equalFactorsGLMeasurable equalFactorsLocalField equalFactorsMeasurable equalFactorsQuotientBorel equalFactorsQuotientMeasurable equalFactorsTopology equalFactorsUnipotentBorel equalFactorsUnipotentMeasurable equalFactorsValuation equalFirstBlockBorel equalFirstBlockGLBorel equalFirstBlockGLMeasurable equalFirstBlockLocalField equalFirstBlockLowerMeasurable equalFirstBlockLowerSeries equalFirstBlockMeasurable equalFirstBlockQuotientMeasurable equalFirstBlockSecondCountable equalFirstBlockTopology equalFirstBlockUnipotentBorel equalFirstBlockUnipotentMeasurable equalFirstBlockValuation equalGammaFamiliesLocalField equalGammaFamiliesQuotientMeasurable equalGammaFamiliesTopology equalGammaFamiliesValuation equalGammaSliceFamilies_entire equalLContinuationGLBorel equalLContinuationGLMeasurable equalLContinuationLocalField equalLContinuationQuotientBorel equalLContinuationQuotientMeasurable equalLContinuationTopology equalLContinuationUnipotentBorel equalLContinuationUnipotentMeasurable equalLContinuationValuation equalLowerFourierCoefficientLaw equalLowerGroupIntegrand_reversedDual equalLowerIntegrand_reversedDual equalModelFiniteClearing_polynomialDivisibility equalNumeratorGLBorel equalNumeratorGLMeasurable equalNumeratorLocalField equalNumeratorQuotientMeasurable equalNumeratorTopology equalNumeratorUnipotentBorel equalNumeratorUnipotentMeasurable equalNumeratorValuation equalRankCoefficient_clearing_of_certificate equalRankCoefficient_continuationData equalRankEntireSliceData equalRank_hasBilateralSpectralExpansion equalRationalGLBorel equalRationalGLMeasurable equalRationalLocalField equalRationalQuotientMeasurable equalRationalTopology equalRationalUnipotentBorel equalRationalUnipotentMeasurable equalRationalValuation equalResidueCardinalityUnit equalSecondBlockBorel equalSecondBlockGLBorel equalSecondBlockGLMeasurable equalSecondBlockLocalField equalSecondBlockMeasurable equalSecondBlockQuotientMeasurable equalSecondBlockSecondCountable equalSecondBlockTopology equalSecondBlockUnipotentBorel equalSecondBlockUnipotentMeasurable equalSecondBlockValuation equalTwoBlockFiniteNumerators_of_laws equalTwoBlockRationalComparison_of_numerators equalTwoBlockSymmetricLBound_at_zero equalTwoBlockSymmetricLBound_of_rationalComparison exists_equalFirstBlockBound_forOrdinaryFunctional exists_equalFirstBlockCoefficientLaw exists_equalOppositeRealRayClearing exists_equalTwoBlockFiniteNumerators exists_equalTwoBlockRationalComparison exists_equalTwoBlockSymmetricLBound exists_equalTwoSidedFirstBlockLaws exists_oppositeWhittakerFamily exists_opposite_coefficient exists_reversedEqualFirstBlockBound firstBlockZeroComparison instBorelSpaceCarrier instMeasurableSpaceCarrier instTopologicalSpaceCarrier inverseWhittaker_secondDual_level_entire inverseWhittaker_translate_level_entire lowerInduced_inverseWhittakerType negatedSelfDualHaar negatedSelfDualHaar_val oppositeDeformationTopology oppositeTwistComparison radicalAverage_eq_equalRankIntegrand reversedDualBlocks_whittakerType reversedDualSectionEquiv_ordinary reversedDual_oppositeTwistBlocks secondDual_oppositeTwistFunctional_val strictModelFiniteClearing_polynomialDivisibility symmetricFactors_of_modelCertificates symmetricLPolynomial_of_modelGenerator unequalRank_hasBilateralSpectralExpansion unfoldedJacquetSeries unfoldedJacquetSeries_eq
open Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg hiding AdjacentRankBaseModelStarIdentity AdjacentRankModelConvergenceStatement AdjacentRankModelStarStatement CentralBilinearVanishingStatement CharacterChangeCompatibleMeasureStatement CorankOneEntireSliceStatement EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankContinuedFormsStatement EqualRankFactorSwapStatement EqualRankFrobeniusStatement EqualRankFunctionalEquationStatement EqualRankGammaExistenceStatement EqualRankLastRowReductionStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement EqualRankTrilinearMirabolicPrerequisites EqualRankTrilinearPrerequisites EqualRankTrilinearUniquenessStatement EqualRankUnitValueStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement LowerFirstBlockIntegrationInputStatement LowerFirstBlockSliceTowerInputStatement NormalizedProductWhittakerTypeStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RankOneCharacterReductionStatement RankOneGammaTwistStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement RootTorusProductStatement SliceIntegrable SliceIntegrableAt SymmetricLPolynomialExistenceStatement TwoBlockDualSectionJacquetStatement TwoBlockFirstBlockLaurentIdentityStatement TwoBlockFirstBlockQuotientIntegrationStatement TwoBlockFixedSliceUnfoldingStatement TwoBlockGammaAdjacentRankStatement TwoBlockGammaDominantRankStatement TwoBlockGammaRankOneStatement TwoBlockJacquetConvergenceStatement TwoBlockLAdjacentRankStatement TwoBlockLDominantRankStatement TwoBlockLRankOneStatement TwoBlockLowerFirstBlockQuotientIntegrationStatement TwoBlockLowerFixedSliceConvergenceStatement TwoBlockOrdinaryJacquetFunctionalStatement TwoBlockSecondWhittakerDeformationStatement TwoBlockUnipotentQuotientIntegrationStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UniformFiniteFunctionMellinConvergenceStatement UnipotentCharacterChangeModulusStatement UnramifiedTwistLFactorStatement WhittakerRowSliceCompactSupportStatement WhittakerTypeGammaConstructionInputStatement ZeroRowLastRowCutoffStatement adjacentRankFullFourier adjacentRankFullFourier_inverseTranspose adjacentRankFullFourier_tmul adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelStar adjacentRankModelStarBase_of_pure_integrals adjacentRankModelStarIntegrabilityLocalInstance1 adjacentRankModelStarIntegrabilityLocalInstance2 adjacentRankModelStarIntegrabilityLocalInstance3 adjacentRankModelStarIntegrabilityLocalInstance4 adjacentRankModelStarIntegrabilityLocalInstance5 adjacentRankModelStarIntegrabilityLocalInstance6 adjacentRankModelStarIntegrabilityLocalInstance7 adjacentRankModelStarIntegrabilityLocalInstance8 adjacentRankModelStarIntegrabilityLocalInstance9 adjacentRankModelStarSourceFunction_regularity adjacentRankModelStarTargetFunction_regularity adjacentRankModelStar_base adjacentRankModelStar_equality_of_base adjacentRankModelStar_pure_right_averages adjacentRankPure_hasCompactSupport adjacentRankTransformedIntegrand adjacentRankTransformedPure_hasCompactSupport adjacentRankTransformed_integrable_of_isSmooth adjacentRank_distribHaarChar adjacentRank_fullFourier_kernel_reflected_orbit adjacentRank_fullFourier_rowTranslate adjacentRank_inverseTranspose_unipotent_epsilon adjacentRank_kernel_reflected_right_orbit adjacentRank_kernel_right_unipotent adjacentRank_partialFourier_rowTranslate adjacentRank_rho0_kernel_right_orbit assembleLowerFirstBlockQuotientIntegration centralBilinearVanishing centralSpectralElement centralSpectralElement_det_abs centralSpectralElement_mem_center characterChangeCompatibleMeasure characterChangeCompatibleMeasure_of_unipotentModulus continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice determinantWeight_centralSpectralElement diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankAnalytic equalRankCompactRootExpansion equalRankContinuedForms equalRankFactorSwap equalRankFrobenius equalRankFunctionalEquation equalRankGammaExistence equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankLastRowReduction equalRankNormalizedCompactIntegration equalRankQuotientAnalytic equalRankRootAverageAnalytic equalRankRootExpansion equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport equalRankTrilinearPrerequisites_of_mirabolic equalRankTrilinearUniqueness equalRankTrilinearUniqueness_of_mirabolic_prerequisites equalRankTrilinearUniqueness_of_prerequisites equalRankUnitValue exists_adjacentRank_lastColumn_bound exists_iwasawa_diagonal_le_of_simpleRoot exists_rankOneCutoff exists_rankOneEmbedding_support exists_schwartzBruhat_row_bound finiteFunctionMellin finiteFunctionShellSeries generalLinearDeterminantSlice hasCompactSupport_matrixSlice hasEqualRankCompactTest_of_kirillov hasSum_setIntegral_determinantSlice iUnion_determinantSlice inverseUniformizer_normalizedAbsoluteValue isClopen_determinantSlice isClopen_generalLinearDeterminantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOfWhittakerType_quasicharacter_twist_iff isOpen_determinantSlice isPadicPairEpsilonFactor_swap_equalRank isPadicPairGammaFactor_swap_equalRank isPadicPairLPolynomial_swap_equalRank isPadicPairLPolynomial_twist isPadicPairLPolynomial_unramified_of_transport isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricGammaFactor_rankOne_test_twist isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt isPadicSymmetricLPolynomial_rankOne_test_twist isPadicSymmetricLPolynomial_twist isPadicSymmetricLPolynomial_unramified_of_transport iwasawaTorusSum lastRowCompactOrbit leviModulus_characterChangeLevi leviModulus_characterChangeLevi_eq_pow lowerFirstBlockIntegrationInput_of_sliceTower lowerFirstBlockSliceTowerInput matrixSliceTest matrixSliceTest_apply measurableSet_determinantSlice mem_determinantSlice mem_generalLinearDeterminantSlice mirabolic_exists_exception_length_le_one mirabolic_pair_control_of_statements mirabolic_shift_length_bound mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer modelStarBaseBorel modelStarBaseDisconnected modelStarBaseGLBorel modelStarBaseGLMeasurable modelStarBaseLocalField modelStarBaseMeasurable modelStarBaseT2 modelStarBaseTopology modelStarBaseUnipotentBorel modelStarBaseUnipotentMeasurable modelStarBaseValuative modelStarFourierBorel modelStarFourierDisconnected modelStarFourierLocalField modelStarFourierMeasurable modelStarFourierT2 modelStarFourierTopology modelStarFourierValuative modelStarOrbitFourierBorel modelStarOrbitFourierDisconnected modelStarOrbitFourierLocalField modelStarOrbitFourierMeasurable modelStarOrbitFourierSecondCountable modelStarOrbitFourierT2 modelStarOrbitFourierTopology modelStarOrbitFourierValuative modelStarReductionBorel modelStarReductionDisconnected modelStarReductionGLBorel modelStarReductionGLMeasurable modelStarReductionLocalField modelStarReductionMeasurable modelStarReductionT2 modelStarReductionTopology modelStarReductionValuative modelStarRegularityLocalField modelStarRegularityTopology modelStarRegularityValuative normalizedAbs_det_of_mem_generalLinearDeterminantSlice normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow normalizedProductWhittakerType oneVariableMellin padicPairGammaConstructionInput_iff padicPairGammaConstructionInput_of_whittakerType padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType padic_quotient_sigmaFinite padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice quasicharacterSmoothCharacter quasicharacter_isOpen_ker quotientHaarExistence quotientIwasawaIntegration quotientRootIntegration rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneGammaTwist rankOneMatrixWhittakerComparison rankOneMatrixWhittakerComparison_of_positive rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct setIntegral_equalRankIntegrand_determinantSlice setIntegral_unequalRankAverage_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrableAt_unequalRankAverage_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice symmetricLPolynomialExists twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockDualSectionJacquet twoBlockFirstBlockLaurentIdentity twoBlockFirstBlockQuotientIntegration twoBlockFixedSliceUnfolding twoBlockGammaRankOne_of_trivial_test twoBlockJacquetConvergence twoBlockLRankOne_of_trivial_test twoBlockLowerFirstBlockQuotientIntegration twoBlockLowerFixedSliceConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val twoBlockOrdinaryJacquetFunctional twoBlockSecondDeformedBlocks twoBlockSecondDeformedBlocks_zero twoBlockSecondDeformedInduced twoBlockSecondWhittakerDeformation twoBlockUnipotentQuotientIntegration twoBlockWhittakerDeformation unequalRankAnalytic unequalRankAverage unequalRankAverage_eq_mul_spectralPoint_zpow unequalRankCommonGenerator unequalRankCompactSupport unequalRankFiniteExpansion unequalRankFunctionalEquation unequalRankGammaPropagation unequalRankIntegrand_eq_mul_spectralPoint_zpow unequalRankIwasawaSupport unequalRankSliceCoefficient unequalRankSliceExpansion unequalRankSliceExpansion_of_converges unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unequalSliceMatrixMeasurable unequalSliceQuotientBorel unequalSliceQuotientMeasurable unequalSliceTopology unipotentCharacterChangeModulus unipotentHaar_mul_diagonal_le unipotentVolumeLocalField unipotentVolumeTopology unipotentVolumeValuativeRel unramifiedTwistLFactor unramifiedTwistLFactor_of_transport whittakerRationalValues_eq_rankOneModelValues whittakerRowSliceCompactSupport whittakerTypeGammaConstructionInput zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding AdjacentRankUnipotentFourierStatement PadicMatrixFourierSliceStatement PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement TwoBlockRowFourierCompanionStatement adjacentRankUnipotentFourier exists_rowSchwartz_order_lower_bound padicLatticeGeometry padicMatrixFourierSlice padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists padicUnipotentHaar_iota_fourier_duality_right twoBlockRowFourierCompanion
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding CompactLocalizationStatement MirabolicCompactTwistedPairingStatement MirabolicFiniteLengthStatement MirabolicFunctionalMultiplicityStatement MirabolicTwistedPairingRigidityStatement MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier UnipotentOrbitStatement compactLocalization exchangedParabolic exists_compactOpen_glCoefficientRightStabilizer functionalsCongr hasCompactSupport_twoBlockCellRestriction inducedLocalization_of_prerequisites mirabolicCompactTwistedPairing mirabolicFiniteLength mirabolicFunctionalMultiplicity mirabolicTwistedPairingRigidity mirabolicUnitTest modelKirillovTransfer mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentOrbit unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.ParameterSpecialization

universe uF uV uW

section Translation




end Translation

section ScalarEquation

open Langlands.LocalFactor hiding coe_residueReflection residueReflection
open Langlands.AllField.LocalFactor

end ScalarEquation

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance equalGammaFamiliesT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance equalGammaFamiliesMeasurable : MeasurableSpace F := borel _
local instance equalGammaFamiliesBorel : BorelSpace F := ⟨rfl⟩
local instance equalGammaFamiliesGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance equalGammaFamiliesGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance equalGammaFamiliesUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance equalGammaFamiliesUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
local instance equalGammaFamiliesQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F) := borel _
local instance equalGammaFamiliesQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩

local notation "T" => (⟨⟩ : LocalFieldData F)
local notation "abv" => normalizedAbsoluteValue T

section Entire

variable {n : ℕ} (ψ : UnitaryAdditiveCharacter F)
  (U : ℂ → InverseWhittakerFunctions ψ n)
  (K : Subgroup (GeneralLinear (n + 1) F))
  (hKo : IsOpen (K : Set (GeneralLinear (n + 1) F)))
  (hKc : IsCompact (K : Set (GeneralLinear (n + 1) F)))
  (hK : ∀ (u : ℂ) (g : GeneralLinear (n + 1) F) (k : K),
    (U u).val (g * k) = (U u).val g)
  (hU : ∀ (g : GeneralLinear (n + 1) F) (u : ℂ),
    AnalyticAt ℂ (fun z => (U z).val g) u)

include K hKo hKc hK hU

/-- A fixed translate retains a common compact open level and entire values. -/
theorem inverseWhittaker_translate_level_entire (a : GeneralLinear (n + 1) F) :
    (∃ L : Subgroup (GeneralLinear (n + 1) F),
      IsOpen (L : Set (GeneralLinear (n + 1) F)) ∧
      IsCompact (L : Set (GeneralLinear (n + 1) F)) ∧
      ∀ (u : ℂ) (g : GeneralLinear (n + 1) F) (k : L),
        (translateInverseWhittaker ψ (U u) a).val (g * k) =
          (translateInverseWhittaker ψ (U u) a).val g) ∧
    ∀ (g : GeneralLinear (n + 1) F) (u : ℂ),
      AnalyticAt ℂ (fun z => (translateInverseWhittaker ψ (U z) a).val g) u := by
  let e : GeneralLinear (n + 1) F ≃ₜ GeneralLinear (n + 1) F :=
    (Homeomorph.mulLeft a⁻¹).trans (Homeomorph.mulRight a)
  let L := K.comap (MulAut.conj a⁻¹).toMonoidHom
  have hL : (L : Set (GeneralLinear (n + 1) F)) = e ⁻¹' K := by
    ext k
    simp [L, e]
  refine ⟨⟨L, ?_, ?_, ?_⟩, fun g u => hU (g * a) u⟩
  · rw [hL]
    exact e.isOpen_preimage.mpr hKo
  · rw [hL]
    exact e.isCompact_preimage.mpr hKc
  · intro u g k
    have hk : a⁻¹ * k.val * a ∈ K := by
      have hk' := k.property
      change a⁻¹ * k.val * (a⁻¹)⁻¹ ∈ K at hk'
      simpa only [inv_inv] using hk'
    change (U u).val ((g * k.val) * a) = (U u).val (g * a)
    have heq : (g * k.val) * a = (g * a) * (a⁻¹ * k.val * a) := by
      simp only [mul_assoc, mul_inv_cancel_left]
    rw [heq]
    exact hK u (g * a) ⟨_, hk⟩

/-- The actual second dual pulls the common level back by inverse transpose. -/
theorem inverseWhittaker_secondDual_level_entire :
    (∃ L : Subgroup (GeneralLinear (n + 1) F),
      IsOpen (L : Set (GeneralLinear (n + 1) F)) ∧
      IsCompact (L : Set (GeneralLinear (n + 1) F)) ∧
      ∀ (u : ℂ) (g : GeneralLinear (n + 1) F) (k : L),
        (secondDualFunction ψ n (U u)).val (g * k) =
          (secondDualFunction ψ n (U u)).val g) ∧
    ∀ (g : GeneralLinear (n + 1) F) (u : ℂ),
      AnalyticAt ℂ (fun z => (secondDualFunction ψ n (U z)).val g) u := by
  let e := inverseTransposeContinuous (n + 1) F
  let L := K.comap e.toMonoidHom
  refine ⟨⟨L, e.toHomeomorph.isOpen_preimage.mpr hKo,
    e.toHomeomorph.isCompact_preimage.mpr hKc, ?_⟩, fun g u => hU _ u⟩
  intro u g k
  change (U u).val (weylLong (n + 1) F *
      inverseTranspose (n + 1) F (g * k.val)) =
    (U u).val (weylLong (n + 1) F *
      inverseTranspose (n + 1) F g)
  rw [map_mul, ← mul_assoc]
  exact hK u _ ⟨e k.val, k.property⟩

variable (μ : Measure (LeftUnipotentQuotient n F)) [IsFiniteMeasureOnCompacts μ]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (n + 1) F) V)
  (hπ : IsOfWhittakerType n (standardCharacter ψ n) π)
  (lambda : glFunctionals ψ n π) (f : (coefficientModel π lambda).toSubmodule)
  (Φ Φhat : SchwartzBruhat (Fin (n + 1) → F))

include hπ

/-- Both literal slice families used for sign-absorbed gamma continuation
are entire; no parameter-dependent scalar is divided out. -/
theorem equalGammaSliceFamilies_entire :
    EntireCoefficientFamily (fun u =>
      equalRankSliceCoefficient T μ ψ f.val
        (translateInverseWhittaker ψ (U u) ((-1) ^ n)) Φ) ∧
    EntireCoefficientFamily (fun u =>
      equalRankSliceCoefficient T μ (ψ.scale (-1)) (firstDualFunction ψ n f.val)
        (secondDualFunction ψ n (U u)) Φhat) := by
  obtain ⟨⟨L, hLo, -, hL⟩, hUa⟩ :=
    inverseWhittaker_translate_level_entire F ψ U K hKo hKc hK hU ((-1) ^ n)
  obtain ⟨⟨Ld, hLdo, -, hLd⟩, hUda⟩ :=
    inverseWhittaker_secondDual_level_entire F ψ U K hKo hKc hK hU
  exact ⟨(equalRankEntireSliceData F ψ μ π lambda f Φ
      (fun u => translateInverseWhittaker ψ (U u) ((-1) ^ n)) hπ.1.1
      L hLo hL hUa).2,
    (equalRankEntireSliceData F (ψ.scale (-1)) μ (inverseTransposePullback π)
      (firstDualFunctional ψ π lambda) (firstDualModelMap ψ π lambda f) Φhat
      (fun u => secondDualFunction ψ n (U u))
      (isOfWhittakerType_firstDual ψ π hπ).1.1 Ld hLdo hLd hUda).2⟩

end Entire

end Langlands.AllField.RankinSelberg.DominantRankTransport
