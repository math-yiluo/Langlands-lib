import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualRational
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantCoefficientContinuation
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantEqualNumerators
/-! # Actual rational comparison and L clearing at equal rank -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg.DominantRankTransport hiding EqualFirstBlockCoefficientLaw EqualFirstBlockFactorCertificate EqualLowerFourierCoefficientLaw EqualModelFiniteClearing EqualTwoBlockFiniteNumerators EqualTwoBlockRationalComparison EqualTwoSidedFirstBlockLaws StrictModelFiniteClearing coe_equalResidueCardinalityUnit coefficientContinuationMatrixMeasurable coefficientContinuationQuotientMeasurable coefficientContinuationTopology determinantComplexPower_inverseTranspose determinantComplexPower_weylLong dualJacquetLocalField dualJacquetTopology dualJacquetValuation equalDualityBorel equalDualityGLBorel equalDualityGLMeasurable equalDualityLocalField equalDualityLowerBorel equalDualityLowerMeasurable equalDualityMeasurable equalDualityQuotientMeasurable equalDualityTopology equalDualityUnipotentBorel equalDualityUnipotentMeasurable equalDualityValuation equalFirstBlockBorel equalFirstBlockGLBorel equalFirstBlockGLMeasurable equalFirstBlockLocalField equalFirstBlockLowerMeasurable equalFirstBlockLowerSeries equalFirstBlockMeasurable equalFirstBlockQuotientMeasurable equalFirstBlockSecondCountable equalFirstBlockTopology equalFirstBlockUnipotentBorel equalFirstBlockUnipotentMeasurable equalFirstBlockValuation equalLowerFourierCoefficientLaw equalLowerGroupIntegrand_reversedDual equalLowerIntegrand_reversedDual equalModelFiniteClearing_polynomialDivisibility equalNumeratorGLBorel equalNumeratorGLMeasurable equalNumeratorLocalField equalNumeratorQuotientMeasurable equalNumeratorTopology equalNumeratorUnipotentBorel equalNumeratorUnipotentMeasurable equalNumeratorValuation equalRank_hasBilateralSpectralExpansion equalRationalGLBorel equalRationalGLMeasurable equalRationalLocalField equalRationalQuotientMeasurable equalRationalTopology equalRationalUnipotentBorel equalRationalUnipotentMeasurable equalRationalValuation equalResidueCardinalityUnit equalSecondBlockBorel equalSecondBlockGLBorel equalSecondBlockGLMeasurable equalSecondBlockLocalField equalSecondBlockMeasurable equalSecondBlockQuotientMeasurable equalSecondBlockSecondCountable equalSecondBlockTopology equalSecondBlockUnipotentBorel equalSecondBlockUnipotentMeasurable equalSecondBlockValuation equalTwoBlockFiniteNumerators_of_laws equalTwoBlockRationalComparison_of_numerators exists_equalFirstBlockBound_forOrdinaryFunctional exists_equalFirstBlockCoefficientLaw exists_equalTwoBlockFiniteNumerators exists_equalTwoBlockRationalComparison exists_equalTwoSidedFirstBlockLaws exists_reversedEqualFirstBlockBound instBorelSpaceCarrier instMeasurableSpaceCarrier instTopologicalSpaceCarrier lowerInduced_inverseWhittakerType negatedSelfDualHaar negatedSelfDualHaar_val radicalAverage_eq_equalRankIntegrand reversedDualBlocks_whittakerType reversedDualSectionEquiv_ordinary reversedDual_oppositeTwistBlocks secondDual_oppositeTwistFunctional_val strictModelFiniteClearing_polynomialDivisibility unequalRank_hasBilateralSpectralExpansion unfoldedJacquetSeries unfoldedJacquetSeries_eq
open Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg hiding AdjacentRankBaseModelStarIdentity AdjacentRankModelConvergenceStatement AdjacentRankModelStarStatement CharacterChangeCompatibleMeasureStatement EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankContinuedFormsStatement EqualRankFactorSwapStatement EqualRankFrobeniusStatement EqualRankFunctionalEquationStatement EqualRankLastRowReductionStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement EqualRankTrilinearUniquenessStatement EqualRankUnitValueStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement LowerFirstBlockIntegrationInputStatement LowerFirstBlockSliceTowerInputStatement NormalizedProductWhittakerTypeStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RankOneCharacterReductionStatement RankOneGammaTwistStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement RootTorusProductStatement SliceIntegrable SliceIntegrableAt SymmetricLPolynomialExistenceStatement TwoBlockDualSectionJacquetStatement TwoBlockFirstBlockLaurentIdentityStatement TwoBlockFirstBlockQuotientIntegrationStatement TwoBlockFixedSliceUnfoldingStatement TwoBlockGammaAdjacentRankStatement TwoBlockGammaDominantRankStatement TwoBlockGammaRankOneStatement TwoBlockJacquetConvergenceStatement TwoBlockLAdjacentRankStatement TwoBlockLDominantRankStatement TwoBlockLRankOneStatement TwoBlockLowerFirstBlockQuotientIntegrationStatement TwoBlockLowerFixedSliceConvergenceStatement TwoBlockOrdinaryJacquetFunctionalStatement TwoBlockUnipotentQuotientIntegrationStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UniformFiniteFunctionMellinConvergenceStatement UnipotentCharacterChangeModulusStatement WhittakerRowSliceCompactSupportStatement ZeroRowLastRowCutoffStatement adjacentRankFullFourier adjacentRankFullFourier_inverseTranspose adjacentRankFullFourier_tmul adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelStar adjacentRankModelStarBase_of_pure_integrals adjacentRankModelStarIntegrabilityLocalInstance1 adjacentRankModelStarIntegrabilityLocalInstance2 adjacentRankModelStarIntegrabilityLocalInstance3 adjacentRankModelStarIntegrabilityLocalInstance4 adjacentRankModelStarIntegrabilityLocalInstance5 adjacentRankModelStarIntegrabilityLocalInstance6 adjacentRankModelStarIntegrabilityLocalInstance7 adjacentRankModelStarIntegrabilityLocalInstance8 adjacentRankModelStarIntegrabilityLocalInstance9 adjacentRankModelStarSourceFunction_regularity adjacentRankModelStarTargetFunction_regularity adjacentRankModelStar_base adjacentRankModelStar_equality_of_base adjacentRankModelStar_pure_right_averages adjacentRankPure_hasCompactSupport adjacentRankTransformedIntegrand adjacentRankTransformedPure_hasCompactSupport adjacentRankTransformed_integrable_of_isSmooth adjacentRank_distribHaarChar adjacentRank_fullFourier_kernel_reflected_orbit adjacentRank_fullFourier_rowTranslate adjacentRank_inverseTranspose_unipotent_epsilon adjacentRank_kernel_reflected_right_orbit adjacentRank_kernel_right_unipotent adjacentRank_partialFourier_rowTranslate adjacentRank_rho0_kernel_right_orbit assembleLowerFirstBlockQuotientIntegration characterChangeCompatibleMeasure characterChangeCompatibleMeasure_of_unipotentModulus continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankAnalytic equalRankCompactRootExpansion equalRankContinuedForms equalRankFactorSwap equalRankFrobenius equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankLastRowReduction equalRankNormalizedCompactIntegration equalRankQuotientAnalytic equalRankRootAverageAnalytic equalRankRootExpansion equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport equalRankUnitValue exists_adjacentRank_lastColumn_bound exists_iwasawa_diagonal_le_of_simpleRoot exists_rankOneCutoff exists_rankOneEmbedding_support exists_schwartzBruhat_row_bound finiteFunctionMellin finiteFunctionShellSeries generalLinearDeterminantSlice hasCompactSupport_matrixSlice hasEqualRankCompactTest_of_kirillov hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClopen_generalLinearDeterminantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOfWhittakerType_quasicharacter_twist_iff isOpen_determinantSlice isPadicPairEpsilonFactor_swap_equalRank isPadicPairGammaFactor_swap_equalRank isPadicPairLPolynomial_swap_equalRank isPadicPairLPolynomial_twist isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricGammaFactor_rankOne_test_twist isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt isPadicSymmetricLPolynomial_rankOne_test_twist isPadicSymmetricLPolynomial_twist iwasawaTorusSum lastRowCompactOrbit leviModulus_characterChangeLevi leviModulus_characterChangeLevi_eq_pow lowerFirstBlockIntegrationInput_of_sliceTower lowerFirstBlockSliceTowerInput matrixSliceTest matrixSliceTest_apply measurableSet_determinantSlice mem_determinantSlice mem_generalLinearDeterminantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer modelStarBaseBorel modelStarBaseDisconnected modelStarBaseGLBorel modelStarBaseGLMeasurable modelStarBaseLocalField modelStarBaseMeasurable modelStarBaseT2 modelStarBaseTopology modelStarBaseUnipotentBorel modelStarBaseUnipotentMeasurable modelStarBaseValuative modelStarFourierBorel modelStarFourierDisconnected modelStarFourierLocalField modelStarFourierMeasurable modelStarFourierT2 modelStarFourierTopology modelStarFourierValuative modelStarOrbitFourierBorel modelStarOrbitFourierDisconnected modelStarOrbitFourierLocalField modelStarOrbitFourierMeasurable modelStarOrbitFourierSecondCountable modelStarOrbitFourierT2 modelStarOrbitFourierTopology modelStarOrbitFourierValuative modelStarReductionBorel modelStarReductionDisconnected modelStarReductionGLBorel modelStarReductionGLMeasurable modelStarReductionLocalField modelStarReductionMeasurable modelStarReductionT2 modelStarReductionTopology modelStarReductionValuative modelStarRegularityLocalField modelStarRegularityTopology modelStarRegularityValuative normalizedAbs_det_of_mem_generalLinearDeterminantSlice normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow normalizedProductWhittakerType oneVariableMellin padicPairGammaConstructionInput_iff padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType padic_quotient_sigmaFinite padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice quasicharacterSmoothCharacter quasicharacter_isOpen_ker quotientHaarExistence quotientIwasawaIntegration quotientRootIntegration rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneGammaTwist rankOneMatrixWhittakerComparison rankOneMatrixWhittakerComparison_of_positive rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct setIntegral_equalRankIntegrand_determinantSlice setIntegral_unequalRankAverage_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrableAt_unequalRankAverage_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice symmetricLPolynomialExists twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockDualSectionJacquet twoBlockFirstBlockLaurentIdentity twoBlockFirstBlockQuotientIntegration twoBlockFixedSliceUnfolding twoBlockGammaRankOne_of_trivial_test twoBlockJacquetConvergence twoBlockLRankOne_of_trivial_test twoBlockLowerFirstBlockQuotientIntegration twoBlockLowerFixedSliceConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val twoBlockOrdinaryJacquetFunctional twoBlockUnipotentQuotientIntegration unequalRankAnalytic unequalRankAverage unequalRankAverage_eq_mul_spectralPoint_zpow unequalRankCommonGenerator unequalRankCompactSupport unequalRankFiniteExpansion unequalRankFunctionalEquation unequalRankGammaPropagation unequalRankIntegrand_eq_mul_spectralPoint_zpow unequalRankIwasawaSupport unequalRankSliceCoefficient unequalRankSliceExpansion unequalRankSliceExpansion_of_converges unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unequalSliceMatrixMeasurable unequalSliceQuotientBorel unequalSliceQuotientMeasurable unequalSliceTopology unipotentCharacterChangeModulus unipotentHaar_mul_diagonal_le unipotentVolumeLocalField unipotentVolumeTopology unipotentVolumeValuativeRel whittakerRationalValues_eq_rankOneModelValues whittakerRowSliceCompactSupport zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
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
open Langlands.RankinSelberg.TwoBlockDominantRectangular hiding AbsoluteInput FiberIntegrable KernelAbsoluteIntegrable KernelNormProfileIntegrable KernelOuterIntegrable NormProfileIntegrable OuterIntegrable absoluteInput_standard_iff ae_lowerQuotientMeasure_iff determinantWeight_lowerBlockUnipotent_mul dualKernelLocalField dualKernelMeasurable dualKernelTopology dualKernelValuation dualRectangleBorel dualRectangleLocalField dualRectangleMatrixBorel dualRectangleMatrixSecondCountable dualRectangleMeasurable dualRectangleProductBorel dualRectangleSecondCountable dualRectangleTopology dualRectangleValuation fiberIntegrable_lowerBlockUnipotent_mul_iff integrable_lowerQuotientMeasure_iff integrable_rectangleChange_iff integral_dualRectangleEquiv integral_rectangleChange kernel kernelAbsoluteIntegrable_iff kernelAbsoluteIntegrable_standard_iff kernel_covariance kernel_eq kernel_reversedDual measurePreserving_dualRectangleEquiv measurePreserving_rectangleChange outerFieldT2 outerFieldTopology outerFieldValuation outerGeneralLinearGroup outerGeneralLinearLocallyCompact outerGeneralLinearSecondCountable outerLocalField quotientFiberIntegrable quotientKernel quotientKernelMeasurable quotientKernelTopology quotientKernel_mk quotientKernel_reversedDual quotientNormProfile quotientNormProfile_mk rawKernel rawKernel_covariance rawKernel_reversedDual rawScalarValue rectangleChangeHomeomorph rectangleHaarBorel rectangleHaarLocalField rectangleHaarMeasurable rectangleHaarSecondCountable rectangleHaarTopology rectangleHaarValuation rectangleMatrixBorel rectangleMatrixSecondCountable rectangleMeasure rectangleMeasure_sigmaFinite rectanglesBorel representativeKernel representativeKernel_lowerBlockUnipotent_mul representativeKernel_reversedDual representativeNormProfile representativeNormProfile_lowerBlockUnipotent_mul reversedDualSectionEquiv reversedDualSectionEquiv_scalar standardCompatible standardCompatible_sigmaFinite
open Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.LocalFactor
open Langlands.AllField.LocalFactor
open Langlands.HarmonicAnalysis.BilateralLaurentSeries

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance equalRationalT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance equalRationalSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance equalRationalMeasurable : MeasurableSpace F := borel _
local instance equalRationalBorel : BorelSpace F := ⟨rfl⟩
local instance equalRationalDisconnected : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance equalRationalGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance equalRationalGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance equalRationalUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance equalRationalUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
local instance equalRationalQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F) := borel _
local instance equalRationalQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
  [hmod : ∀ i, Module ℂ (W i)]

local notation "qF" => (Langlands.LocalFieldData.residueCardinality (⟨⟩ : LocalFieldData F))
local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

variable (ψ : UnitaryAdditiveCharacter F)
  (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (t + 1) F) V)
  (lambda : glFunctionals ψ t π)
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
  (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
  (hσ : ∀ i, IsSmooth (σ i))
  (J : glInverseFunctionals ψ t (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ))
  (μN : Measure (LeftUnipotentQuotient t F))
  (μA : Measure (LeftUnipotentQuotient (m 0) F))
  (μB : Measure (LeftUnipotentQuotient (m 1) F))

/-- Actual original and reversed rational integrals, with both complete block
certificates, uniform finite clearing and the intrinsic L bound. -/
def EqualTwoBlockRationalComparison : Prop :=
  let E := reversedDualSectionEquiv F h σ hσ
  let σD := fun i : Fin 2 => inverseTransposePullback (σ i.rev)
  let ellD := fun i : Fin 2 => secondDualFunctional ψ (σ i.rev) (ell i.rev)
  let JD := transportedSecondDualFunctional ψ (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) E J
  let q := equalResidueCardinalityUnit F
  ∃ (ζ₁ c₁ ζ₂ c₂ : ℂˣ) (d₁ d₂ : ℤ) (P₁ P₁D P₂ P₂D : Polynomial ℂ),
    EqualFirstBlockFactorCertificate F h ψ ν π lambda σ ell μA ζ₁ c₁ d₁ P₁ P₁D ∧
    EqualFirstBlockFactorCertificate F (reverse_sum h) (ψ.scale (-1))
      (negatedSelfDualHaar F ψ ν) (inverseTransposePullback π)
      (firstDualFunctional ψ π lambda) σD ellD μB ζ₂ c₂ d₂ P₂D P₂ ∧
    (∀ (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σ)
      (Wtest : (coefficientModel π lambda).toSubmodule)
      (Φ Φhat : SchwartzBruhat (Fin (t + 1) → F)),
      IsRowFourierPair ψ ν.val Φ Φhat →
      ∃ R RD : RationalFunctions,
        HasRationalContinuation qF
          (fun s => equalRankIntegral ψ abv μN Wtest.val
            (modelMap (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) J f).val Φ s) R ∧
        HasRationalContinuation qF
          (fun s => equalRankIntegral (ψ.scale (-1)) abv μN
            (firstDualModelMap ψ π lambda Wtest).val
            (modelMap (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F (reverse_sum h) σD) JD (E f)).val
            Φhat s) RD ∧
        RationalReflection.subst q⁻¹
            (laurentToRatFunc (P₁D * P₂D).toLaurent * RD) =
          laurentToRatFunc
              (↑(clearedProductMultiplierUnit q (ζ₁ ^ t * c₁) d₁
                (ζ₂ ^ t * c₂) d₂) : LaurentPolynomial ℂ) *
            laurentToRatFunc (P₁ * P₂).toLaurent * R) ∧
    EqualModelFiniteClearing F ψ μN π (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ)
      lambda J (P₁ * P₂) ∧
    ∀ P : Polynomial ℂ,
      IsEqualRankLPolynomial qF ψ abv μN π (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) P →
      ∃ (Q : Polynomial ℂ) (e : ℕ), Polynomial.X ^ e * (P₁ * P₂) = Q * P

set_option maxHeartbeats 1600000 in
/-- Published convergence and rationality turn the actual finite numerators
into rational identities; model surjectivity gives the full intrinsic L bound. -/
theorem equalTwoBlockRationalComparison_of_numerators
    [Measure.IsMulRightInvariant (unipotentHaar F t)]
    (hμN : IsCompatible (upperUnipotent (t + 1) F)
      (generalLinearHaar F t) (unipotentHaar F t) μN)
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (hσtype : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (hlambda : lambda.val ≠ 0) (hJ0 : J.val ≠ 0)
    (hnum : EqualTwoBlockFiniteNumerators F h ψ ν π lambda σ ell hσ J μN μA μB) :
    EqualTwoBlockRationalComparison F h ψ ν π lambda σ ell hσ J μN μA μB := by
  let E := reversedDualSectionEquiv F h σ hσ
  let σD := fun i : Fin 2 => inverseTransposePullback (σ i.rev)
  let JD := transportedSecondDualFunctional ψ (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) E J
  let q := equalResidueCardinalityUnit F
  obtain ⟨ζ₁, c₁, ζ₂, c₂, d₁, d₂, P₁, P₁D, P₂, P₂D,
    hcert₁, hcert₂, hfinite⟩ := hnum
  have hInd := lowerInduced_inverseWhittakerType F h ψ σ hσtype
  have hAn := equalRankAnalytic F (⟨⟩ : LocalFieldData F) t ψ μN hμN
    V (Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σ) π (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ)
    hπ hInd lambda J hlambda hJ0
  have hπD : IsOfWhittakerType t (standardCharacter (ψ.scale (-1)) t)
      (inverseTransposePullback π) := by
    simpa only [standardCharacter_scale_neg_one] using
      isOfWhittakerType_inverseTransposePullback ψ π hπ
  have hσD := reversedDualBlocks_whittakerType F σ ψ hσtype
  have hIndD := lowerInduced_inverseWhittakerType F (reverse_sum h)
    (ψ.scale (-1)) σD hσD
  have hAnD := equalRankAnalytic F (⟨⟩ : LocalFieldData F) t (ψ.scale (-1)) μN hμN
    V (Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F (reverse_sum h) σD) (inverseTransposePullback π)
    (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F (reverse_sum h) σD)
    hπD hIndD (firstDualFunctional ψ π lambda) JD
    (firstDualFunctional_ne_zero ψ π hlambda)
    (transportedSecondDualFunctional_ne_zero ψ (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) E hJ0)
  have hclear : EqualModelFiniteClearing F ψ μN π (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ)
      lambda J (P₁ * P₂) := by
    intro U U' Φ
    obtain ⟨f, hf⟩ := modelMap_surjective (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) J U'
    obtain ⟨Φhat, hpair⟩ := (rowFourierCompatibility ψ ν.val (t + 1) ν.property).1 Φ
    obtain ⟨N, hN, -⟩ := hfinite f U Φ Φhat hpair
    exact ⟨N, by simpa only [hf] using hN.1⟩
  have hP₁ : P₁ ≠ 0 := by
    have hsum : (m 0 + 1) + (m 1 + 1) = t + 1 := by
      simpa only [Fin.sum_univ_two] using h
    exact (hcert₁.2.2 0 (m 1) (by omega)).1.polynomial_ne_zero
  have hP₂ : P₂ ≠ 0 := by
    have hsum : (m 0 + 1) + (m 1 + 1) = t + 1 := by
      simpa only [Fin.sum_univ_two] using h
    exact (hcert₂.2.2 0 (m 0) (by
      change t = m 1 + (0 + m 0 + 1)
      omega)).2.polynomial_ne_zero
  refine ⟨ζ₁, c₁, ζ₂, c₂, d₁, d₂, P₁, P₁D, P₂, P₂D,
    hcert₁, hcert₂, ?_, hclear, ?_⟩
  · intro f Wtest Φ Φhat hpair
    let U' := modelMap (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) J f
    let UD := firstDualModelMap ψ π lambda Wtest
    let U'D := modelMap (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F (reverse_sum h) σD) JD (E f)
    obtain ⟨R, hR⟩ := hAn.2.1 Wtest U' Φ
    obtain ⟨RD, hRD⟩ := hAnD.2.1 UD U'D Φhat
    refine ⟨R, RD, hR, hRD, ?_⟩
    have hexp := equalRank_hasBilateralSpectralExpansion F ψ μN Wtest.val U'.val Φ
      (hAn.1 Wtest U' Φ)
    have hexpD := equalRank_hasBilateralSpectralExpansion F (ψ.scale (-1)) μN
      UD.val U'D.val Φhat (hAnD.1 UD U'D Φhat)
    obtain ⟨N, hN, -⟩ := hfinite f Wtest Φ Φhat hpair
    exact reflectedNumerators_rationalIdentity
      (⟨⟩ : LocalFieldData F).residueCardinality_gt_one q
      (P₁ * P₂).toLaurent (P₁D * P₂D).toLaurent
      (clearedProductMultiplierUnit q (ζ₁ ^ t * c₁) d₁ (ζ₂ ^ t * c₂) d₂) R RD
      hexp hexpD ⟨N, hN⟩ hR hRD
  · intro P hP
    exact equalModelFiniteClearing_polynomialDivisibility F ψ μN π
      (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) lambda J hπ hInd hlambda hJ0
      P (P₁ * P₂) (mul_ne_zero hP₁ hP₂) hP hclear

omit σ ell hσ J μN μA μB in
/-- Above a common real opposite-twist bound, actual ordinary Jacquet
functionals give the rational comparison and intrinsic L bound. -/
theorem exists_equalTwoBlockRationalComparison
    [Measure.IsMulRightInvariant (unipotentHaar F t)]
    [Measure.IsMulRightInvariant (unipotentHaar F (m 0))]
    [Measure.IsMulRightInvariant (unipotentHaar F (m 1))]
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
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
          EqualTwoBlockRationalComparison F h ψ ν π lambda σu ellu hσu Ju μN μA μB := by
  obtain ⟨Cbound, hCbound⟩ := exists_equalTwoBlockFiniteNumerators F h ψ ν π lambda
    hπ hlambda τ hτ ell0 hell0
  refine ⟨Cbound, fun u hu => ?_⟩
  dsimp only
  obtain ⟨habs, Ju, hJu0, hJu, hnum⟩ := hCbound u hu
  refine ⟨habs, Ju, hJu0, hJu, ?_⟩
  intro μN μA μB hμN hμA hμB
  exact equalTwoBlockRationalComparison_of_numerators F h ψ ν π lambda
    (twoBlockOppositeTwistBlocks F m τ u)
    (fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i))
    (fun i => ((twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u i _).2
      (hτ i)).1.1)
    Ju μN μA μB hμN hπ
    (fun i => (twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u i _).2 (hτ i))
    hlambda hJu0 (hnum μN μA μB hμN hμA hμB)

end Langlands.AllField.RankinSelberg.DominantRankTransport
