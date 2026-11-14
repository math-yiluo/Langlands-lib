import Langlands.Representation.RankinSelberg.AdjacentRankProductDenominatorBound
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankMatrixWitnesses
/-! The product of the two certified ordinary polynomials bounds realized corank values. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg.Padic hiding AdjacentRankCoefficientConvolution AdjacentRankCorankDenominatorBound AdjacentRankModelConverges AdjacentRankProductContinuationData AdjacentRankShellConvolutionAt AdjacentRankShellLowerBounds adjacentRankBeforeShearKernel adjacentRankBeforeShearKernel_mk adjacentRankCoefficientConvolution_of_shell adjacentRankCompact_middleAverage adjacentRankCompact_middleAverage_and_dual adjacentRankDualInnerSliceIntegral adjacentRankDualMiddleAverage adjacentRankDualMiddleAverage_eq adjacentRankFiniteProductValue adjacentRankInnerMultiplier adjacentRankInnerMultiplier_mul adjacentRankInnerSliceWeight adjacentRankInnerSliceWeight_mul adjacentRankInnerSlice_matchedFiniteSeparation adjacentRankJointShell adjacentRankJointShellKernel adjacentRankJointShellKernel_mk adjacentRankJointShellKernel_mk_eq_innerSlice adjacentRankMatrixSliceCoefficient adjacentRankMatrixSliceCoefficient_eq_zero_of_pointwise_bound adjacentRankMatrixSliceExpansion adjacentRankModelConverges_of_isSmooth adjacentRankModelIntegral adjacentRankModelIntegral_mul adjacentRankModelIntegral_separated_rankInclusion_raw adjacentRankModelIntegral_separated_rankInclusion_weighted adjacentRankModelMap adjacentRankModelMapBorel adjacentRankModelMapDisconnected adjacentRankModelMapGLMeasurable adjacentRankModelMapLocalField adjacentRankModelMapMeasurable adjacentRankModelMapT2 adjacentRankModelMapTopology adjacentRankModelMapValuative adjacentRankModelMap_apply adjacentRankModelStarScalar adjacentRankModelStar_corankOneSlice_eq_before adjacentRankModelStar_separated_rankInclusion adjacentRankModelStar_separated_rankInclusion_weighted adjacentRankModel_corankOneSlice_eq_before adjacentRankModel_matchedCoefficientConvolution adjacentRankModel_matchedProductContinuation adjacentRankModel_matchedProductContinuation_exists adjacentRankProductContinuation_denominatorBound adjacentRankSeparatedTest_rho0_rankInclusion adjacentRankShell_finiteConvolution_of_innerSeparation adjacentRankShell_matchedFiniteConvolution adjacentRankShell_shear_fubini compactCoefficientsBorel compactCoefficientsLocalField compactCoefficientsMeasurable compactCoefficientsTopology compactCoefficientsValuativeRel continuationFieldMeasurableSpace continuationFieldTopology continuationFieldValuation continuationGroupBorelSpace continuationGroupMeasurableSpace continuationLocalField continuationQuotientMeasurableSpace continuationUnipotentBorelSpace continuationUnipotentMeasurableSpace continuous_adjacentRankInnerMultiplier continuous_adjacentRankInnerSliceWeight continuous_adjacentRankJointShellKernel corankOneCoefficient_convergesOnRight corankOneCoefficient_productContinuation corankOneCoefficient_scalarProductContinuation corankOneIntegral_eq_finiteProducts_of_coefficients corankOneIntegrand_eq_mul_spectralPoint_zpow corankOneSliceExpansion dualCompactFieldTopology dualCompactGroupBorel dualCompactGroupMeasurable dualCompactLocalField dualCompactValuativeRel dualModelFieldBorel dualModelFieldMeasurable dualModelFieldT2 dualModelFieldTopology dualModelFieldTotallyDisconnected dualModelGroupBorel dualModelGroupMeasurable dualModelLocalField dualModelValuativeRel dualRestrictionFieldBorel dualRestrictionFieldMeasurable dualRestrictionFieldT2 dualRestrictionFieldTopology dualRestrictionFieldTotallyDisconnected dualRestrictionGroupBorel dualRestrictionGroupMeasurable dualRestrictionLocalField dualRestrictionValuativeRel equalRankSliceCoefficient_eq_zero_of_pointwise_bound exists_adjacentRankInner_subgroup exists_adjacentRankModelMatrixValues exists_matrixTest_determinantOrder_lowerBound exists_whittakerRow_determinantOrder_lowerBound hasCompactSupport_adjacentRankInnerSliceWeight hasCompactSupport_adjacentRankJointShellKernel hasCompactSupport_equalRankSlice hasSum_setIntegral_generalLinearDeterminantSlice innerSliceFieldTopology innerSliceGroupBorel innerSliceGroupMeasurable innerSliceLocalField innerSliceValuativeRel instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instTotallyDisconnectedSpaceCarrier instValuativeRelCarrier integrable_adjacentRankInnerSliceWeight_mul integrable_adjacentRankJointShellKernel integrable_equalRankSlice integral_eq_sum_determinantSlices inverseCoefficientAsScaledStandard isClopen_adjacentRankJointShell jointShellFieldT2 jointShellFieldTopology jointShellGroupBorelSpace jointShellGroupMeasurableSpace jointShellGroupSecondCountable jointShellGroupSigmaCompact jointShellLocalField jointShellQuotientBorelSpace jointShellQuotientMeasurableSpace jointShellQuotientT2 jointShellValuativeRel matchedCoefficientFieldBorel matchedCoefficientFieldMeasurable matchedCoefficientFieldT2 matchedCoefficientFieldTopology matchedCoefficientFieldTotallyDisconnected matchedCoefficientGroupBorel matchedCoefficientGroupMeasurable matchedCoefficientGroupSigmaCompact matchedCoefficientLocalField matchedCoefficientQuotientBorel matchedCoefficientQuotientMeasurable matchedCoefficientUnipotentBorel matchedCoefficientUnipotentMeasurable matchedCoefficientValuativeRel matchedContinuationFieldBorel matchedContinuationFieldMeasurable matchedContinuationFieldT2 matchedContinuationFieldTopology matchedContinuationFieldTotallyDisconnected matchedContinuationGroupBorel matchedContinuationGroupMeasurable matchedContinuationLocalField matchedContinuationQuotientMeasurable matchedContinuationUnipotentBorel matchedContinuationUnipotentMeasurable matchedContinuationValuativeRel matchedInnerFieldTopology matchedInnerGroupBorel matchedInnerGroupMeasurable matchedInnerGroupSecondCountable matchedInnerGroupSigmaCompact matchedInnerLocalField matchedInnerValuativeRel matchedShellFieldT2 matchedShellFieldTopology matchedShellGroupBorel matchedShellGroupMeasurable matchedShellGroupSecondCountable matchedShellGroupSigmaCompact matchedShellLocalField matchedShellQuotientLocallyCompact matchedShellQuotientMeasurable matchedShellQuotientSecondCountable matchedShellUnipotentBorel matchedShellUnipotentMeasurable matchedShellValuativeRel matrixWitnessFieldBorel matrixWitnessFieldMeasurable matrixWitnessFieldT2 matrixWitnessFieldTotallyDisconnected matrixWitnessGroupBorel matrixWitnessGroupMeasurable matrixWitnessLocalField matrixWitnessQuotientMeasurable matrixWitnessTopology matrixWitnessUnipotentBorel matrixWitnessUnipotentMeasurable matrixWitnessValuativeRel modelZetaFieldBorel modelZetaFieldMeasurable modelZetaFieldT2 modelZetaFieldTopology modelZetaFieldTotallyDisconnected modelZetaGroupBorel modelZetaGroupMeasurable modelZetaLocalField modelZetaValuativeRel productBoundFieldMeasurable productBoundGroupBorel productBoundGroupMeasurable productBoundLocalField productBoundModelAddCommGroup productBoundQuotientMeasurable productBoundTopology productBoundUnipotentBorel productBoundUnipotentMeasurable productBoundValuativeRel productsFieldTopology productsQuotientMeasurableSpace quotientShearFieldT2 quotientShearFieldTopology quotientShearGroupBorel quotientShearGroupMeasurable quotientShearGroupSecondCountable quotientShearGroupSigmaCompact quotientShearLocalField quotientShearQuotientBorel quotientShearQuotientLocallyCompact quotientShearQuotientMeasurable quotientShearQuotientSecondCountable quotientShearUnipotentBorel quotientShearUnipotentMeasurable quotientShearValuativeRel scaledStandardCoefficientAsInverse setIntegral_matrixIntegrand_determinantSlice shellConvolutionFieldTopology shellConvolutionLocalField shellConvolutionQuotientBorel shellConvolutionQuotientMeasurable shellConvolutionValuativeRel spectralFieldTopology spectralFieldValuation spectralGroupBorelSpace spectralGroupMeasurableSpace spectralLocalField spectralQuotientBorelSpace spectralQuotientMeasurableSpace
open Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg hiding AdjacentRankBaseModelStarIdentity AdjacentRankModelConvergenceStatement AdjacentRankModelConverges AdjacentRankModelStarStatement CharacterChangeCompatibleMeasureStatement EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankContinuedFormsStatement EqualRankFactorSwapStatement EqualRankFunctionalEquationStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement EqualRankUnitValueStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RankOneCharacterReductionStatement RankOneGammaTwistStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement RootTorusProductStatement SliceIntegrable SliceIntegrableAt SymmetricLPolynomialExistenceStatement TwoBlockGammaAdjacentRankStatement TwoBlockGammaDominantRankStatement TwoBlockGammaRankOneStatement TwoBlockLAdjacentRankStatement TwoBlockLDominantRankStatement TwoBlockLRankOneStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UniformFiniteFunctionMellinConvergenceStatement UnipotentCharacterChangeModulusStatement WhittakerRowSliceCompactSupportStatement ZeroRowLastRowCutoffStatement adjacentRankFullFourier adjacentRankFullFourier_inverseTranspose adjacentRankFullFourier_tmul adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelIntegral adjacentRankModelIntegrand adjacentRankModelStar adjacentRankModelStarBase_of_pure_integrals adjacentRankModelStarIntegrabilityLocalInstance1 adjacentRankModelStarIntegrabilityLocalInstance2 adjacentRankModelStarIntegrabilityLocalInstance3 adjacentRankModelStarIntegrabilityLocalInstance4 adjacentRankModelStarIntegrabilityLocalInstance5 adjacentRankModelStarIntegrabilityLocalInstance6 adjacentRankModelStarIntegrabilityLocalInstance7 adjacentRankModelStarIntegrabilityLocalInstance8 adjacentRankModelStarIntegrabilityLocalInstance9 adjacentRankModelStarSourceFunction_regularity adjacentRankModelStarTargetFunction_regularity adjacentRankModelStar_base adjacentRankModelStar_equality_of_base adjacentRankModelStar_pure_right_averages adjacentRankPure_hasCompactSupport adjacentRankStarEquiv adjacentRankStarEquiv_tmul_evaluation adjacentRankTransformedIntegrand adjacentRankTransformedPure_hasCompactSupport adjacentRankTransformed_integrable_of_isSmooth adjacentRank_distribHaarChar adjacentRank_fullFourier_kernel_reflected_orbit adjacentRank_fullFourier_rowTranslate adjacentRank_inverseTranspose_unipotent_epsilon adjacentRank_kernel_reflected_right_orbit adjacentRank_kernel_right_unipotent adjacentRank_partialFourier_rowTranslate adjacentRank_rho0_kernel_right_orbit characterChangeCompatibleMeasure characterChangeCompatibleMeasure_of_unipotentModulus continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankAnalytic equalRankCompactRootExpansion equalRankContinuedForms equalRankFactorSwap equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankNormalizedCompactIntegration equalRankQuotientAnalytic equalRankRootAverageAnalytic equalRankRootExpansion equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport equalRankUnitValue exists_adjacentRank_lastColumn_bound exists_iwasawa_diagonal_le_of_simpleRoot exists_rankOneCutoff exists_rankOneEmbedding_support exists_schwartzBruhat_row_bound finiteFunctionMellin finiteFunctionShellSeries generalLinearDeterminantSlice hasCompactSupport_matrixSlice hasEqualRankCompactTest_of_kirillov hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClopen_generalLinearDeterminantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOfWhittakerType_quasicharacter_twist_iff isOpen_determinantSlice isPadicPairEpsilonFactor_swap_equalRank isPadicPairGammaFactor_swap_equalRank isPadicPairLPolynomial_swap_equalRank isPadicPairLPolynomial_twist isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricGammaFactor_rankOne_test_twist isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt isPadicSymmetricLPolynomial_rankOne_test_twist isPadicSymmetricLPolynomial_twist iwasawaTorusSum lastRowCompactOrbit leviModulus_characterChangeLevi leviModulus_characterChangeLevi_eq_pow matrixSliceTest matrixSliceTest_apply measurableSet_determinantSlice mem_determinantSlice mem_generalLinearDeterminantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer modelStarBaseBorel modelStarBaseDisconnected modelStarBaseGLBorel modelStarBaseGLMeasurable modelStarBaseLocalField modelStarBaseMeasurable modelStarBaseT2 modelStarBaseTopology modelStarBaseUnipotentBorel modelStarBaseUnipotentMeasurable modelStarBaseValuative modelStarFourierBorel modelStarFourierDisconnected modelStarFourierLocalField modelStarFourierMeasurable modelStarFourierT2 modelStarFourierTopology modelStarFourierValuative modelStarOrbitFourierBorel modelStarOrbitFourierDisconnected modelStarOrbitFourierLocalField modelStarOrbitFourierMeasurable modelStarOrbitFourierSecondCountable modelStarOrbitFourierT2 modelStarOrbitFourierTopology modelStarOrbitFourierValuative modelStarReductionBorel modelStarReductionDisconnected modelStarReductionGLBorel modelStarReductionGLMeasurable modelStarReductionLocalField modelStarReductionMeasurable modelStarReductionT2 modelStarReductionTopology modelStarReductionValuative modelStarRegularityLocalField modelStarRegularityTopology modelStarRegularityValuative normalizedAbs_det_of_mem_generalLinearDeterminantSlice normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow oneVariableMellin padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice quasicharacterSmoothCharacter quasicharacter_isOpen_ker quotientHaarExistence quotientIwasawaIntegration quotientRootIntegration rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneGammaTwist rankOneMatrixWhittakerComparison rankOneMatrixWhittakerComparison_of_positive rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice symmetricLPolynomialExists twoBlockGammaRankOne_of_trivial_test twoBlockLRankOne_of_trivial_test unequalRankAnalytic unequalRankCommonGenerator unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIwasawaSupport unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unipotentCharacterChangeModulus unipotentHaar_mul_diagonal_le unipotentVolumeLocalField unipotentVolumeTopology unipotentVolumeValuativeRel whittakerRationalValues_eq_rankOneModelValues whittakerRowSliceCompactSupport zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding AdjacentRankUnipotentFourierStatement PadicMatrixFourierSliceStatement PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement adjacentRankUnipotentFourier padicLatticeGeometry padicMatrixFourierSlice padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists padicUnipotentHaar_iota_fourier_duality_right
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement exists_compactOpen_glCoefficientRightStabilizer mirabolicUnitTest modelKirillovTransfer smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.QuotientIntegration
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open scoped BigOperators

universe uF uV uW uU

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance productBoundFieldMeasurable : MeasurableSpace F := borel _
local instance productBoundGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F) := borel _
local instance productBoundGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F) := ⟨rfl⟩
local instance productBoundUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F) := borel _
local instance productBoundUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F) := ⟨rfl⟩
local instance productBoundQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F) := borel _

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)
local notation "qF" => (Langlands.LocalFieldData.residueCardinality (⟨⟩ : LocalFieldData F))

attribute [local irreducible] GodementJacquet.biSmoothMatrixCoefficients
  coefficientModel modelRepresentation

local instance productBoundModelAddCommGroup
    (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (ℓ : glFunctionals ψ r σ) :
    AddCommGroup (glCoefficientModel ψ r σ ℓ).toSubmodule :=
  (glCoefficientModel ψ r σ ℓ).toSubmodule.addCommGroup

/-- Every rational continuation of a specified actual corank integral lies
in the Laurent span of the reciprocal of the proposed polynomial. -/
def AdjacentRankCorankDenominatorBound
    {r : ℕ} (ψ : UnitaryAdditiveCharacter F)
    (ν : Measure (LeftUnipotentQuotient r F))
    (U : WhittakerFunctions ψ (r + 1)) (W' : InverseWhittakerFunctions ψ r)
    (P : Polynomial ℂ) : Prop :=
  ∀ R : RationalFunctions,
    HasRationalContinuation qF (fun s => corankOneIntegral ψ abv ν U W' s) R →
      R ∈ Submodule.span LaurentCoefficients
        {(algebraMap (Polynomial ℂ) RationalFunctions P)⁻¹}

/-- The actual matched finite product belongs to the reciprocal Laurent span
of the product of the supplied complete equal-rank and twisted rank-one
polynomial certificates. No factor-existence or image-equality claim is made. -/
theorem adjacentRankProductContinuation_denominatorBound
    (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    {r N : ℕ} [Measure.IsMulRightInvariant (unipotentHaar F r)]
    (ν : Measure (LeftUnipotentQuotient r F))
    (hν : IsCompatible (upperUnipotent (r + 1) F)
      (generalLinearHaar F r) (unipotentHaar F r) ν)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (ℓ : glFunctionals ψ r σ)
    (τ : Representation ℂ (GeneralLinear (r + 1) F) V')
    (hτ : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) τ)
    (ℓ' : glFunctionals (ψ.scale (-1)) r τ) (hℓ' : ℓ'.val ≠ 0)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (B : Fin N → (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule)
    (U : WhittakerFunctions ψ (r + 1)) (W' : InverseWhittakerFunctions ψ r)
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (φ : SchwartzBruhat (Fin (r + 1) → F))
    (χ : Quasicharacter F)
    (f : Fin N → GodementJacquet.biSmoothMatrixCoefficients
      (V := (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule)
      (glModelRepresentation (ψ.scale (-1)) r τ ℓ'))
    (M : Fin N → RationalFunctions) (c : ℂ)
    (hM : ∀ i, GodementJacquet.HasShiftedRationalValue qF abv
      (generalLinearHaar F r) Φ
      (fun h => (χ (determinant h) : ℂ) * (f i).val h) (M i))
    (hdata : AdjacentRankProductContinuationData F ψ ν W.val
      (fun i => InducedTailIntermediate.scaledStandardAsInverse ψ (B i).val)
      U W' Φ φ χ (fun i => (f i).val) M c)
    (P₀ P₁ : Polynomial ℂ)
    (hP₀ : IsPadicSymmetricLPolynomial F ψ μ σ τ P₀)
    (hP₁ : IsPadicSymmetricLPolynomial F (ψ.scale (-1)) μ
      (Langlands.twist ((χ : Fˣ →* ℂˣ).comp determinant) τ)
      (rankOneCharacter 1) P₁) :
    AdjacentRankCorankDenominatorBound F ψ ν U W' (P₀ * P₁) := by
  classical
  let τT := Langlands.twist ((χ : Fˣ →* ℂˣ).comp determinant) τ
  let ℓT := determinantTwistFunctionalEquiv (ψ.scale (-1)) χ τ ℓ'
  have hτT : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) τT :=
    (isOfWhittakerType_quasicharacter_twist_iff (⟨⟩ : LocalFieldData F)
      (ψ.scale (-1)) χ τ).mpr hτ
  have hℓT : ℓT.val ≠ 0 := hℓ'
  let hopen := quasicharacter_isOpen_ker (⟨⟩ : LocalFieldData F) χ
  let fT i := GodementJacquet.determinantTwistModelCoefficient
    (ψ.scale (-1)) χ hopen τ ℓ' (f i)
  have hgen₁ : Langlands.AllField.GodementJacquet.Padic.IsMatrixNormalizedGenerator F
      (V := (glCoefficientModel (ψ.scale (-1)) r τT ℓT).toSubmodule)
      (glModelRepresentation (ψ.scale (-1)) r τT ℓT) P₁ :=
    Langlands.AllField.GodementJacquet.Padic.isMatrixNormalizedGenerator_model_of_pair
    F (ψ.scale (-1)) τT μ hτT hP₁ ℓT hℓT
  have hPair₀ : IsPadicPairLPolynomial F ψ μ σ τ P₀ :=
    (isPadicSymmetricLPolynomial_of_le (Nat.le_refl r)).mp hP₀
  have hEq₀ : IsPairLPolynomial qF ψ abv ν μ σ τ P₀ := hPair₀.2 ν hν
  have hgen₀ : IsNormalizedGenerator (equalRankZetaValues qF ψ abv ν σ τ) P₀ :=
    (isPairLPolynomial_self (π := σ) (σ := τ)).mp hEq₀
  have hprod := GodementJacquet.normalizedGenerator_productRationalValues hgen₀ hgen₁
  obtain ⟨A, hA, ⟨a, ha⟩, -, huniq⟩ := hdata
  have hAmem (i : Fin N) : A i ∈ equalRankZetaValues qF ψ abv ν σ τ := by
    refine ⟨W.val, coefficientModel_subset_whittakerSet ℓ W.property,
      InducedTailIntermediate.scaledStandardAsInverse ψ (B i).val, ?_, φ,
      ⟨a, fun s hs => (ha s hs).2.1 i⟩, hA i⟩
    exact coefficientModel_subset_inverseWhittakerSet
      (functionalsCongr (standardCharacter_scale_neg_one ψ r) ℓ')
      (scaledStandardCoefficientAsInverse F ψ τ ℓ' (B i)).property
  have hMmem (i : Fin N) : M i ∈ GodementJacquet.matrixRationalValues
      (V := (glCoefficientModel (ψ.scale (-1)) r τT ℓT).toSubmodule) qF abv
      (generalLinearHaar F r)
      (glModelRepresentation (ψ.scale (-1)) r τT ℓT) :=
    ⟨Φ, fT i, hM i⟩
  have hsum : (∑ i, A i * M i) ∈ zetaSpan (GodementJacquet.productRationalValues
      (equalRankZetaValues qF ψ abv ν σ τ)
      (GodementJacquet.matrixRationalValues
        (V := (glCoefficientModel (ψ.scale (-1)) r τT ℓT).toSubmodule)
        qF abv (generalLinearHaar F r)
        (glModelRepresentation (ψ.scale (-1)) r τT ℓT))) := by
    apply Submodule.sum_mem
    intro i _
    exact mem_zetaSpan (GodementJacquet.mem_productRationalValues.mpr
      ⟨A i, hAmem i, M i, hMmem i, rfl⟩)
  intro R hR
  rw [huniq R hR]
  exact hprod.2 ▸ GodementJacquet.const_mul_mem_zetaSpan c hsum

end Langlands.AllField.RankinSelberg.Padic
