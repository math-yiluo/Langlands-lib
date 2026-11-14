import Langlands.Representation.RankinSelberg.AdjacentRankMatrixWitnesses
import Langlands.AllField.Representation.GodementJacquet.ModelMatrixAnalyticData
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankMatchedProductContinuation
import Langlands.AllField.Representation.RankinSelberg.RankOneTestReduction
/-! Actual original and dual matrix witnesses for the matched finite products. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg.Padic hiding AdjacentRankCoefficientConvolution AdjacentRankModelConverges AdjacentRankProductContinuationData AdjacentRankShellConvolutionAt AdjacentRankShellLowerBounds adjacentRankBeforeShearKernel adjacentRankBeforeShearKernel_mk adjacentRankCoefficientConvolution_of_shell adjacentRankCompact_middleAverage adjacentRankCompact_middleAverage_and_dual adjacentRankDualInnerSliceIntegral adjacentRankDualMiddleAverage adjacentRankDualMiddleAverage_eq adjacentRankFiniteProductValue adjacentRankInnerMultiplier adjacentRankInnerMultiplier_mul adjacentRankInnerSliceWeight adjacentRankInnerSliceWeight_mul adjacentRankInnerSlice_matchedFiniteSeparation adjacentRankJointShell adjacentRankJointShellKernel adjacentRankJointShellKernel_mk adjacentRankJointShellKernel_mk_eq_innerSlice adjacentRankMatrixSliceCoefficient adjacentRankMatrixSliceCoefficient_eq_zero_of_pointwise_bound adjacentRankMatrixSliceExpansion adjacentRankModelConverges_of_isSmooth adjacentRankModelIntegral adjacentRankModelIntegral_mul adjacentRankModelIntegral_separated_rankInclusion_raw adjacentRankModelIntegral_separated_rankInclusion_weighted adjacentRankModelMap adjacentRankModelMapBorel adjacentRankModelMapDisconnected adjacentRankModelMapGLMeasurable adjacentRankModelMapLocalField adjacentRankModelMapMeasurable adjacentRankModelMapT2 adjacentRankModelMapTopology adjacentRankModelMapValuative adjacentRankModelMap_apply adjacentRankModelStarScalar adjacentRankModelStar_corankOneSlice_eq_before adjacentRankModelStar_separated_rankInclusion adjacentRankModelStar_separated_rankInclusion_weighted adjacentRankModel_corankOneSlice_eq_before adjacentRankModel_matchedCoefficientConvolution adjacentRankModel_matchedProductContinuation adjacentRankModel_matchedProductContinuation_exists adjacentRankSeparatedTest_rho0_rankInclusion adjacentRankShell_finiteConvolution_of_innerSeparation adjacentRankShell_matchedFiniteConvolution adjacentRankShell_shear_fubini compactCoefficientsBorel compactCoefficientsLocalField compactCoefficientsMeasurable compactCoefficientsTopology compactCoefficientsValuativeRel continuationFieldMeasurableSpace continuationFieldTopology continuationFieldValuation continuationGroupBorelSpace continuationGroupMeasurableSpace continuationLocalField continuationQuotientMeasurableSpace continuationUnipotentBorelSpace continuationUnipotentMeasurableSpace continuous_adjacentRankInnerMultiplier continuous_adjacentRankInnerSliceWeight continuous_adjacentRankJointShellKernel corankOneCoefficient_convergesOnRight corankOneCoefficient_productContinuation corankOneCoefficient_scalarProductContinuation corankOneIntegral_eq_finiteProducts_of_coefficients corankOneIntegrand_eq_mul_spectralPoint_zpow corankOneSliceExpansion dualCompactFieldTopology dualCompactGroupBorel dualCompactGroupMeasurable dualCompactLocalField dualCompactValuativeRel dualModelFieldBorel dualModelFieldMeasurable dualModelFieldT2 dualModelFieldTopology dualModelFieldTotallyDisconnected dualModelGroupBorel dualModelGroupMeasurable dualModelLocalField dualModelValuativeRel dualRestrictionFieldBorel dualRestrictionFieldMeasurable dualRestrictionFieldT2 dualRestrictionFieldTopology dualRestrictionFieldTotallyDisconnected dualRestrictionGroupBorel dualRestrictionGroupMeasurable dualRestrictionLocalField dualRestrictionValuativeRel equalRankSliceCoefficient_eq_zero_of_pointwise_bound exists_adjacentRankInner_subgroup exists_adjacentRankModelMatrixValues exists_matrixTest_determinantOrder_lowerBound exists_whittakerRow_determinantOrder_lowerBound hasCompactSupport_adjacentRankInnerSliceWeight hasCompactSupport_adjacentRankJointShellKernel hasCompactSupport_equalRankSlice hasSum_setIntegral_generalLinearDeterminantSlice innerSliceFieldTopology innerSliceGroupBorel innerSliceGroupMeasurable innerSliceLocalField innerSliceValuativeRel instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instTotallyDisconnectedSpaceCarrier instValuativeRelCarrier integrable_adjacentRankInnerSliceWeight_mul integrable_adjacentRankJointShellKernel integrable_equalRankSlice integral_eq_sum_determinantSlices inverseCoefficientAsScaledStandard isClopen_adjacentRankJointShell jointShellFieldT2 jointShellFieldTopology jointShellGroupBorelSpace jointShellGroupMeasurableSpace jointShellGroupSecondCountable jointShellGroupSigmaCompact jointShellLocalField jointShellQuotientBorelSpace jointShellQuotientMeasurableSpace jointShellQuotientT2 jointShellValuativeRel matchedCoefficientFieldBorel matchedCoefficientFieldMeasurable matchedCoefficientFieldT2 matchedCoefficientFieldTopology matchedCoefficientFieldTotallyDisconnected matchedCoefficientGroupBorel matchedCoefficientGroupMeasurable matchedCoefficientGroupSigmaCompact matchedCoefficientLocalField matchedCoefficientQuotientBorel matchedCoefficientQuotientMeasurable matchedCoefficientUnipotentBorel matchedCoefficientUnipotentMeasurable matchedCoefficientValuativeRel matchedContinuationFieldBorel matchedContinuationFieldMeasurable matchedContinuationFieldT2 matchedContinuationFieldTopology matchedContinuationFieldTotallyDisconnected matchedContinuationGroupBorel matchedContinuationGroupMeasurable matchedContinuationLocalField matchedContinuationQuotientMeasurable matchedContinuationUnipotentBorel matchedContinuationUnipotentMeasurable matchedContinuationValuativeRel matchedInnerFieldTopology matchedInnerGroupBorel matchedInnerGroupMeasurable matchedInnerGroupSecondCountable matchedInnerGroupSigmaCompact matchedInnerLocalField matchedInnerValuativeRel matchedShellFieldT2 matchedShellFieldTopology matchedShellGroupBorel matchedShellGroupMeasurable matchedShellGroupSecondCountable matchedShellGroupSigmaCompact matchedShellLocalField matchedShellQuotientLocallyCompact matchedShellQuotientMeasurable matchedShellQuotientSecondCountable matchedShellUnipotentBorel matchedShellUnipotentMeasurable matchedShellValuativeRel matrixWitnessFieldBorel matrixWitnessFieldMeasurable matrixWitnessFieldT2 matrixWitnessFieldTotallyDisconnected matrixWitnessGroupBorel matrixWitnessGroupMeasurable matrixWitnessLocalField matrixWitnessQuotientMeasurable matrixWitnessTopology matrixWitnessUnipotentBorel matrixWitnessUnipotentMeasurable matrixWitnessValuativeRel modelZetaFieldBorel modelZetaFieldMeasurable modelZetaFieldT2 modelZetaFieldTopology modelZetaFieldTotallyDisconnected modelZetaGroupBorel modelZetaGroupMeasurable modelZetaLocalField modelZetaValuativeRel productsFieldTopology productsQuotientMeasurableSpace quotientShearFieldT2 quotientShearFieldTopology quotientShearGroupBorel quotientShearGroupMeasurable quotientShearGroupSecondCountable quotientShearGroupSigmaCompact quotientShearLocalField quotientShearQuotientBorel quotientShearQuotientLocallyCompact quotientShearQuotientMeasurable quotientShearQuotientSecondCountable quotientShearUnipotentBorel quotientShearUnipotentMeasurable quotientShearValuativeRel scaledStandardCoefficientAsInverse setIntegral_matrixIntegrand_determinantSlice shellConvolutionFieldTopology shellConvolutionLocalField shellConvolutionQuotientBorel shellConvolutionQuotientMeasurable shellConvolutionValuativeRel spectralFieldTopology spectralFieldValuation spectralGroupBorelSpace spectralGroupMeasurableSpace spectralLocalField spectralQuotientBorelSpace spectralQuotientMeasurableSpace
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

local instance matrixWitnessFieldT2 : T2Space F :=
  (⟨⟩ : LocalFieldData F).fieldT2
local instance matrixWitnessFieldTotallyDisconnected :
    TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance matrixWitnessFieldMeasurable : MeasurableSpace F := borel _
local instance matrixWitnessFieldBorel : BorelSpace F := ⟨rfl⟩
local instance matrixWitnessGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F) := borel _
local instance matrixWitnessGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F) := ⟨rfl⟩
local instance matrixWitnessUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F) := borel _
local instance matrixWitnessUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F) := ⟨rfl⟩
local instance matrixWitnessQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F) := borel _

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)
local notation "qF" => (Langlands.LocalFieldData.residueCardinality (⟨⟩ : LocalFieldData F))

attribute [local irreducible] GodementJacquet.biSmoothMatrixCoefficients
  coefficientModel modelRepresentation

/-- Both literal determinant-twisted matrix functions have actual shifted
rational values. The constructed coefficient models, full type and nonzero
functionals discharge the published model-rationality theorem's hypotheses. -/
theorem exists_adjacentRankModelMatrixValues
    (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hτ : IsOfWhittakerType r (standardCharacter ψ r) τ)
    (ℓ : glFunctionals ψ r τ) (hℓ : ℓ.val ≠ 0)
    (χ : Quasicharacter F)
    (Φ ΦD : GodementJacquet.MatrixTestFunction r F)
    (f : GodementJacquet.biSmoothMatrixCoefficients
      (V := (glCoefficientModel ψ r τ ℓ).toSubmodule)
      (glModelRepresentation ψ r τ ℓ)) :
    ∃ M MD : RationalFunctions,
      GodementJacquet.HasShiftedRationalValue qF abv
        (generalLinearHaar F r) Φ
        (fun h => (χ (determinant h) : ℂ) * f.val h) M ∧
      GodementJacquet.HasShiftedRationalValue qF abv
        (generalLinearHaar F r) ΦD
        (fun h => (χ⁻¹ (determinant h) : ℂ) *
          GodementJacquet.coefficientIota f.val h) MD := by
  let τT := Langlands.twist ((χ : Fˣ →* ℂˣ).comp determinant) τ
  let ℓT := determinantTwistFunctionalEquiv ψ χ τ ℓ
  have hτT : IsOfWhittakerType r (standardCharacter ψ r) τT :=
    (isOfWhittakerType_quasicharacter_twist_iff (⟨⟩ : LocalFieldData F) ψ χ τ).mpr hτ
  have hℓT : ℓT.val ≠ 0 := hℓ
  let hopen := quasicharacter_isOpen_ker (⟨⟩ : LocalFieldData F) χ
  let fT := GodementJacquet.determinantTwistModelCoefficient ψ χ hopen τ ℓ f
  let M := Langlands.AllField.GodementJacquet.Padic.modelMatrixRationalValue F ψ τT hτT ℓT hℓT Φ fT
  have hM := (Langlands.AllField.GodementJacquet.Padic.modelMatrixRationalValue_spec
    F ψ τT hτT ℓT hℓT Φ fT).1
  let τD := inverseTransposePullback τT
  let ℓD := functionalsCongr (standardCharacter_scale_neg_one ψ r).symm
    (dualFunctional ψ τT ℓT)
  have hτD : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) τD := by
    simpa only [standardCharacter_scale_neg_one] using
      isOfWhittakerType_inverseTransposePullback ψ τT hτT
  have hℓD : ℓD.val ≠ 0 := dualFunctional_nonzero ψ τT ℓT hℓT
  let fD := GodementJacquet.iotaDeterminantTwistModelCoefficient ψ χ hopen τ ℓ f
  let MD := Langlands.AllField.GodementJacquet.Padic.modelMatrixRationalValue F (ψ.scale (-1))
    τD hτD ℓD hℓD ΦD fD
  have hMD := (Langlands.AllField.GodementJacquet.Padic.modelMatrixRationalValue_spec
    F (ψ.scale (-1)) τD hτD ℓD hℓD ΦD fD).1
  refine ⟨M, MD, hM, ?_⟩
  have hfD : fD.val = fun h => (χ⁻¹ (determinant h) : ℂ) *
      GodementJacquet.coefficientIota f.val h := by
    funext h
    exact GodementJacquet.iotaDeterminantTwistModelCoefficient_apply ψ χ hopen τ ℓ f h
  simpa only [hfD] using hMD

/-- The matched original and literal dual rational product formulas with
all actual matrix continuations supplied by the published model theorem.
The whole-function realization of the ambient vector is still explicit. -/
theorem adjacentRankModel_matchedProductContinuation_exists
    (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    [Measure.IsMulRightInvariant (unipotentHaar F r)]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    {VU : Type uU} [AddCommGroup VU] [Module ℂ VU]
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
    (ℓ : glFunctionals ψ r σ) (hℓ : ℓ.val ≠ 0)
    (χ : Quasicharacter F)
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (φ φHat : SchwartzBruhat (Fin (r + 1) → F))
    (hφ : IsRowFourierPair ψ μ φ φHat)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (π : Representation ℂ (GeneralLinear (r + 1 + 1) F) VU)
    (hπ : IsOfWhittakerType (r + 1) (standardCharacter ψ (r + 1)) π)
    (ℓU : glFunctionals ψ (r + 1) π) (hℓU : ℓU.val ≠ 0)
    (U : (glCoefficientModel ψ (r + 1) π ℓU).toSubmodule)
    (hU : ∀ g, U.val.val g = adjacentRankModelIntegral F ψ μ hself σ ℓ χ
      (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W) g)
    (τ : Representation ℂ (GeneralLinear (r + 1) F) V')
    (hτ : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) τ)
    (ℓ' : glFunctionals (ψ.scale (-1)) r τ) (hℓ' : ℓ'.val ≠ 0)
    (ν : Measure (LeftUnipotentQuotient r F))
    (hν : IsCompatible (upperUnipotent (r + 1) F)
      (generalLinearHaar F r) (unipotentHaar F r) ν) :
    let ΦD := adjacentRankReflectedTest
      (rectangularFourierEquiv ψ μ (r + 1) (r + 1) hself Φ)
    let WD := inverseCoefficientAsScaledStandard F ψ (inverseTransposePullback σ)
      (dualFunctional ψ σ ℓ) (dualModelLinearMap ψ σ ℓ W)
    let UD := inverseCoefficientAsScaledStandard F ψ (inverseTransposePullback π)
      (dualFunctional ψ π ℓU) (dualModelLinearMap ψ π ℓU U)
    ∃ (N : ℕ)
      (B : Fin N → (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule),
      ∀ W' : (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule,
        ∃ (f : Fin N → GodementJacquet.biSmoothMatrixCoefficients
          (V := (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule)
          (glModelRepresentation (ψ.scale (-1)) r τ ℓ'))
          (M MD : Fin N → RationalFunctions),
          (∀ i, GodementJacquet.HasShiftedRationalValue qF abv
            (generalLinearHaar F r) Φ
            (fun h => (χ (determinant h) : ℂ) * (f i).val h) (M i)) ∧
          (∀ i, GodementJacquet.HasShiftedRationalValue qF abv
            (generalLinearHaar F r) ΦD
            (fun h => (χ⁻¹ (determinant h) : ℂ) *
              GodementJacquet.coefficientIota (f i).val h) (MD i)) ∧
          AdjacentRankProductContinuationData F ψ ν W.val
            (fun i => InducedTailIntermediate.scaledStandardAsInverse ψ (B i).val)
            U.val (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val)
            Φ φ χ (fun i => (f i).val) M 1 ∧
          AdjacentRankProductContinuationData F (ψ.scale (-1)) ν WD.val
            (fun i => (dualModelLinearMap (ψ.scale (-1)) τ ℓ' (B i)).val)
            UD.val (dualModelLinearMap (ψ.scale (-1)) τ ℓ' W').val
            ΦD φHat χ⁻¹ (fun i => GodementJacquet.coefficientIota (f i).val)
            MD (adjacentRankModelStarScalar F χ r) := by
  classical
  dsimp only
  let ΦD := adjacentRankReflectedTest
    (rectangularFourierEquiv ψ μ (r + 1) (r + 1) hself Φ)
  obtain ⟨N, B, hB⟩ := adjacentRankModel_matchedProductContinuation
    F ψ μ hself σ hσ ℓ hℓ χ Φ φ φHat hφ W π hπ ℓU hℓU U hU τ hτ ℓ' hℓ' ν hν
  refine ⟨N, B, fun W' => ?_⟩
  obtain ⟨f, hf⟩ := hB W'
  choose M MD hM hMD using fun i =>
    exists_adjacentRankModelMatrixValues F (ψ.scale (-1)) τ hτ ℓ' hℓ' χ Φ ΦD (f i)
  exact ⟨f, M, MD, hM, hMD, hf M MD hM hMD⟩

end Langlands.AllField.RankinSelberg.Padic
