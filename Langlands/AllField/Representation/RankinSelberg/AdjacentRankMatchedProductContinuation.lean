import Langlands.Representation.RankinSelberg.AdjacentRankMatchedProductContinuation
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankMatchedModelCoefficients
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankProductContinuation
/-! Matched rational finite products for the original and literal dual model. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg.Padic hiding AdjacentRankCoefficientConvolution AdjacentRankModelConverges AdjacentRankProductContinuationData AdjacentRankShellConvolutionAt AdjacentRankShellLowerBounds adjacentRankBeforeShearKernel adjacentRankBeforeShearKernel_mk adjacentRankCoefficientConvolution_of_shell adjacentRankCompact_middleAverage adjacentRankCompact_middleAverage_and_dual adjacentRankDualInnerSliceIntegral adjacentRankDualMiddleAverage adjacentRankDualMiddleAverage_eq adjacentRankFiniteProductValue adjacentRankInnerMultiplier adjacentRankInnerMultiplier_mul adjacentRankInnerSliceWeight adjacentRankInnerSliceWeight_mul adjacentRankInnerSlice_matchedFiniteSeparation adjacentRankJointShell adjacentRankJointShellKernel adjacentRankJointShellKernel_mk adjacentRankJointShellKernel_mk_eq_innerSlice adjacentRankMatrixSliceCoefficient adjacentRankMatrixSliceCoefficient_eq_zero_of_pointwise_bound adjacentRankMatrixSliceExpansion adjacentRankModelConverges_of_isSmooth adjacentRankModelIntegral adjacentRankModelIntegral_mul adjacentRankModelIntegral_separated_rankInclusion_raw adjacentRankModelIntegral_separated_rankInclusion_weighted adjacentRankModelMap adjacentRankModelMapBorel adjacentRankModelMapDisconnected adjacentRankModelMapGLMeasurable adjacentRankModelMapLocalField adjacentRankModelMapMeasurable adjacentRankModelMapT2 adjacentRankModelMapTopology adjacentRankModelMapValuative adjacentRankModelMap_apply adjacentRankModelStarScalar adjacentRankModelStar_corankOneSlice_eq_before adjacentRankModelStar_separated_rankInclusion adjacentRankModelStar_separated_rankInclusion_weighted adjacentRankModel_corankOneSlice_eq_before adjacentRankModel_matchedCoefficientConvolution adjacentRankModel_matchedProductContinuation adjacentRankSeparatedTest_rho0_rankInclusion adjacentRankShell_finiteConvolution_of_innerSeparation adjacentRankShell_matchedFiniteConvolution adjacentRankShell_shear_fubini compactCoefficientsBorel compactCoefficientsLocalField compactCoefficientsMeasurable compactCoefficientsTopology compactCoefficientsValuativeRel continuationFieldMeasurableSpace continuationFieldTopology continuationFieldValuation continuationGroupBorelSpace continuationGroupMeasurableSpace continuationLocalField continuationQuotientMeasurableSpace continuationUnipotentBorelSpace continuationUnipotentMeasurableSpace continuous_adjacentRankInnerMultiplier continuous_adjacentRankInnerSliceWeight continuous_adjacentRankJointShellKernel corankOneCoefficient_convergesOnRight corankOneCoefficient_productContinuation corankOneCoefficient_scalarProductContinuation corankOneIntegral_eq_finiteProducts_of_coefficients corankOneIntegrand_eq_mul_spectralPoint_zpow corankOneSliceExpansion dualCompactFieldTopology dualCompactGroupBorel dualCompactGroupMeasurable dualCompactLocalField dualCompactValuativeRel dualModelFieldBorel dualModelFieldMeasurable dualModelFieldT2 dualModelFieldTopology dualModelFieldTotallyDisconnected dualModelGroupBorel dualModelGroupMeasurable dualModelLocalField dualModelValuativeRel dualRestrictionFieldBorel dualRestrictionFieldMeasurable dualRestrictionFieldT2 dualRestrictionFieldTopology dualRestrictionFieldTotallyDisconnected dualRestrictionGroupBorel dualRestrictionGroupMeasurable dualRestrictionLocalField dualRestrictionValuativeRel equalRankSliceCoefficient_eq_zero_of_pointwise_bound exists_adjacentRankInner_subgroup exists_matrixTest_determinantOrder_lowerBound exists_whittakerRow_determinantOrder_lowerBound hasCompactSupport_adjacentRankInnerSliceWeight hasCompactSupport_adjacentRankJointShellKernel hasCompactSupport_equalRankSlice hasSum_setIntegral_generalLinearDeterminantSlice innerSliceFieldTopology innerSliceGroupBorel innerSliceGroupMeasurable innerSliceLocalField innerSliceValuativeRel instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instTotallyDisconnectedSpaceCarrier instValuativeRelCarrier integrable_adjacentRankInnerSliceWeight_mul integrable_adjacentRankJointShellKernel integrable_equalRankSlice integral_eq_sum_determinantSlices inverseCoefficientAsScaledStandard isClopen_adjacentRankJointShell jointShellFieldT2 jointShellFieldTopology jointShellGroupBorelSpace jointShellGroupMeasurableSpace jointShellGroupSecondCountable jointShellGroupSigmaCompact jointShellLocalField jointShellQuotientBorelSpace jointShellQuotientMeasurableSpace jointShellQuotientT2 jointShellValuativeRel matchedCoefficientFieldBorel matchedCoefficientFieldMeasurable matchedCoefficientFieldT2 matchedCoefficientFieldTopology matchedCoefficientFieldTotallyDisconnected matchedCoefficientGroupBorel matchedCoefficientGroupMeasurable matchedCoefficientGroupSigmaCompact matchedCoefficientLocalField matchedCoefficientQuotientBorel matchedCoefficientQuotientMeasurable matchedCoefficientUnipotentBorel matchedCoefficientUnipotentMeasurable matchedCoefficientValuativeRel matchedContinuationFieldBorel matchedContinuationFieldMeasurable matchedContinuationFieldT2 matchedContinuationFieldTopology matchedContinuationFieldTotallyDisconnected matchedContinuationGroupBorel matchedContinuationGroupMeasurable matchedContinuationLocalField matchedContinuationQuotientMeasurable matchedContinuationUnipotentBorel matchedContinuationUnipotentMeasurable matchedContinuationValuativeRel matchedInnerFieldTopology matchedInnerGroupBorel matchedInnerGroupMeasurable matchedInnerGroupSecondCountable matchedInnerGroupSigmaCompact matchedInnerLocalField matchedInnerValuativeRel matchedShellFieldT2 matchedShellFieldTopology matchedShellGroupBorel matchedShellGroupMeasurable matchedShellGroupSecondCountable matchedShellGroupSigmaCompact matchedShellLocalField matchedShellQuotientLocallyCompact matchedShellQuotientMeasurable matchedShellQuotientSecondCountable matchedShellUnipotentBorel matchedShellUnipotentMeasurable matchedShellValuativeRel modelZetaFieldBorel modelZetaFieldMeasurable modelZetaFieldT2 modelZetaFieldTopology modelZetaFieldTotallyDisconnected modelZetaGroupBorel modelZetaGroupMeasurable modelZetaLocalField modelZetaValuativeRel productsFieldTopology productsQuotientMeasurableSpace quotientShearFieldT2 quotientShearFieldTopology quotientShearGroupBorel quotientShearGroupMeasurable quotientShearGroupSecondCountable quotientShearGroupSigmaCompact quotientShearLocalField quotientShearQuotientBorel quotientShearQuotientLocallyCompact quotientShearQuotientMeasurable quotientShearQuotientSecondCountable quotientShearUnipotentBorel quotientShearUnipotentMeasurable quotientShearValuativeRel scaledStandardCoefficientAsInverse setIntegral_matrixIntegrand_determinantSlice shellConvolutionFieldTopology shellConvolutionLocalField shellConvolutionQuotientBorel shellConvolutionQuotientMeasurable shellConvolutionValuativeRel spectralFieldTopology spectralFieldValuation spectralGroupBorelSpace spectralGroupMeasurableSpace spectralLocalField spectralQuotientBorelSpace spectralQuotientMeasurableSpace
open Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg hiding AdjacentRankBaseModelStarIdentity AdjacentRankModelConvergenceStatement AdjacentRankModelConverges AdjacentRankModelStarStatement EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankContinuedFormsStatement EqualRankFunctionalEquationStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement EqualRankUnitValueStatement FiniteFunctionMellinStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RankOneGammaTwistStatement RootTorusProductStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerRowSliceCompactSupportStatement ZeroRowLastRowCutoffStatement adjacentRankFullFourier adjacentRankFullFourier_inverseTranspose adjacentRankFullFourier_tmul adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelIntegral adjacentRankModelIntegrand adjacentRankModelStar adjacentRankModelStarBase_of_pure_integrals adjacentRankModelStarIntegrabilityLocalInstance1 adjacentRankModelStarIntegrabilityLocalInstance2 adjacentRankModelStarIntegrabilityLocalInstance3 adjacentRankModelStarIntegrabilityLocalInstance4 adjacentRankModelStarIntegrabilityLocalInstance5 adjacentRankModelStarIntegrabilityLocalInstance6 adjacentRankModelStarIntegrabilityLocalInstance7 adjacentRankModelStarIntegrabilityLocalInstance8 adjacentRankModelStarIntegrabilityLocalInstance9 adjacentRankModelStarSourceFunction_regularity adjacentRankModelStarTargetFunction_regularity adjacentRankModelStar_base adjacentRankModelStar_equality_of_base adjacentRankModelStar_pure_right_averages adjacentRankPure_hasCompactSupport adjacentRankStarEquiv adjacentRankStarEquiv_tmul_evaluation adjacentRankTransformedIntegrand adjacentRankTransformedPure_hasCompactSupport adjacentRankTransformed_integrable_of_isSmooth adjacentRank_distribHaarChar adjacentRank_fullFourier_kernel_reflected_orbit adjacentRank_fullFourier_rowTranslate adjacentRank_inverseTranspose_unipotent_epsilon adjacentRank_kernel_reflected_right_orbit adjacentRank_kernel_right_unipotent adjacentRank_partialFourier_rowTranslate adjacentRank_rho0_kernel_right_orbit continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankAnalytic equalRankCompactRootExpansion equalRankContinuedForms equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankNormalizedCompactIntegration equalRankQuotientAnalytic equalRankRootAverageAnalytic equalRankRootExpansion equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport equalRankUnitValue exists_adjacentRank_lastColumn_bound exists_iwasawa_diagonal_le_of_simpleRoot exists_schwartzBruhat_row_bound finiteFunctionMellin finiteFunctionShellSeries generalLinearDeterminantSlice hasCompactSupport_matrixSlice hasEqualRankCompactTest_of_kirillov hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClopen_generalLinearDeterminantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lastRowCompactOrbit matrixSliceTest matrixSliceTest_apply measurableSet_determinantSlice mem_determinantSlice mem_generalLinearDeterminantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer modelStarBaseBorel modelStarBaseDisconnected modelStarBaseGLBorel modelStarBaseGLMeasurable modelStarBaseLocalField modelStarBaseMeasurable modelStarBaseT2 modelStarBaseTopology modelStarBaseUnipotentBorel modelStarBaseUnipotentMeasurable modelStarBaseValuative modelStarFourierBorel modelStarFourierDisconnected modelStarFourierLocalField modelStarFourierMeasurable modelStarFourierT2 modelStarFourierTopology modelStarFourierValuative modelStarOrbitFourierBorel modelStarOrbitFourierDisconnected modelStarOrbitFourierLocalField modelStarOrbitFourierMeasurable modelStarOrbitFourierSecondCountable modelStarOrbitFourierT2 modelStarOrbitFourierTopology modelStarOrbitFourierValuative modelStarReductionBorel modelStarReductionDisconnected modelStarReductionGLBorel modelStarReductionGLMeasurable modelStarReductionLocalField modelStarReductionMeasurable modelStarReductionT2 modelStarReductionTopology modelStarReductionValuative modelStarRegularityLocalField modelStarRegularityTopology modelStarRegularityValuative normalizedAbs_det_of_mem_generalLinearDeterminantSlice normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow oneVariableMellin padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice quotientIwasawaIntegration quotientRootIntegration rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice unequalRankAnalytic unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIwasawaSupport unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion whittakerRowSliceCompactSupport zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding AdjacentRankUnipotentFourierStatement PadicMatrixFourierSliceStatement PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement adjacentRankUnipotentFourier padicMatrixFourierSlice padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicScalarHaarScaling padicUnipotentHaar_iota_fourier_duality_right
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement exists_compactOpen_glCoefficientRightStabilizer mirabolicUnitTest modelKirillovTransfer smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.QuotientIntegration
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open scoped BigOperators

universe uF uV uW uU

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance matchedContinuationFieldT2 : T2Space F :=
  (⟨⟩ : LocalFieldData F).fieldT2
local instance matchedContinuationFieldTotallyDisconnected :
    TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance matchedContinuationFieldMeasurable : MeasurableSpace F := borel _
local instance matchedContinuationFieldBorel : BorelSpace F := ⟨rfl⟩
local instance matchedContinuationGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F) := borel _
local instance matchedContinuationGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F) := ⟨rfl⟩
local instance matchedContinuationUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F) := borel _
local instance matchedContinuationUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F) := ⟨rfl⟩
local instance matchedContinuationQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F) := borel _

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)
local notation "qF" => (Langlands.LocalFieldData.residueCardinality (⟨⟩ : LocalFieldData F))

/-- Actual common-half-plane finite products and their unique rational value,
with the explicit scalar from the model-star restriction. -/
def AdjacentRankProductContinuationData {r N : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Measure (LeftUnipotentQuotient r F))
    (W : WhittakerFunctions ψ r) (B : Fin N → InverseWhittakerFunctions ψ r)
    (U : WhittakerFunctions ψ (r + 1)) (W' : InverseWhittakerFunctions ψ r)
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (φ : SchwartzBruhat (Fin (r + 1) → F))
    (χ : Quasicharacter F)
    (f : Fin N → GeneralLinear (r + 1) F → ℂ)
    (M : Fin N → RationalFunctions) (c : ℂ) : Prop :=
  ∃ A : Fin N → RationalFunctions,
    (∀ i, HasRationalContinuation qF
      (fun s => equalRankIntegral ψ abv ν W (B i) φ s) (A i)) ∧
    (∃ a : ℝ, ∀ s : ℂ, a < s.re →
      CorankOneConverges ψ abv ν U W' s ∧
      (∀ i, EqualRankConverges ψ abv ν W (B i) φ s) ∧
      (∀ i, Langlands.AllField.GodementJacquet.Padic.MatrixConverges F Φ (s + (r : ℂ) / 2)
        (fun h => (χ (determinant h) : ℂ) * f i h)) ∧
      corankOneIntegral ψ abv ν U W' s =
        c * adjacentRankFiniteProductValue F ψ ν W B Φ φ χ f s) ∧
    HasRationalContinuation qF (fun s => corankOneIntegral ψ abv ν U W' s)
      (RatFunc.C c * ∑ i, A i * M i) ∧
    ∀ R, HasRationalContinuation qF (fun s => corankOneIntegral ψ abv ν U W' s) R →
      R = RatFunc.C c * ∑ i, A i * M i

private theorem corankIntegrand_smul {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F) (c : ℂ)
    (U : WhittakerFunctions ψ (r + 1)) (W' : InverseWhittakerFunctions ψ r)
    (s : ℂ) (q : LeftUnipotentQuotient r F) :
    corankOneIntegrand ψ abv (c • U) W' s q =
      c * corankOneIntegrand ψ abv U W' s q := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [corankOneIntegrand_mk, corankOneIntegrand_mk]
    change (c * U.val (rankInclusion 1 g)) * W'.val g *
      determinantWeight abv g (s - 1 / 2) = _
    ring

private theorem corankIntegral_smul {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Measure (LeftUnipotentQuotient r F)) (c : ℂ)
    (U : WhittakerFunctions ψ (r + 1)) (W' : InverseWhittakerFunctions ψ r)
    (s : ℂ) :
    corankOneIntegral ψ abv ν (c • U) W' s =
      c * corankOneIntegral ψ abv ν U W' s := by
  simp only [corankOneIntegral, corankIntegrand_smul, integral_const_mul]

set_option maxHeartbeats 1600000 in
/-- A nonzero scalar in the actual coefficient convolution is retained in
the rational product by rescaling only the ambient coefficient vector. -/
theorem corankOneCoefficient_scalarProductContinuation {r N : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    [Measure.IsMulRightInvariant (unipotentHaar F r)]
    (ν : Measure (LeftUnipotentQuotient r F))
    (hν : IsCompatible (upperUnipotent (r + 1) F)
      (generalLinearHaar F r) (unipotentHaar F r) ν)
    (μ : AdditiveHaarMeasure F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    {VU : Type uU} [AddCommGroup VU] [Module ℂ VU]
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (τ : Representation ℂ (GeneralLinear (r + 1) F) V')
    (π : Representation ℂ (GeneralLinear (r + 1 + 1) F) VU)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
    (hτ : IsOfWhittakerType r (inverseStandardCharacter ψ r) τ)
    (hπ : IsOfWhittakerType (r + 1) (standardCharacter ψ (r + 1)) π)
    (ℓ : glFunctionals ψ r σ) (ℓ' : glInverseFunctionals ψ r τ)
    (ℓU : glFunctionals ψ (r + 1) π)
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0) (hℓU : ℓU.val ≠ 0)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (B : Fin N → (coefficientModel τ ℓ').toSubmodule)
    (U : (glCoefficientModel ψ (r + 1) π ℓU).toSubmodule)
    (W' : (coefficientModel τ ℓ').toSubmodule)
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (φ : SchwartzBruhat (Fin (r + 1) → F))
    (χ : Quasicharacter F)
    (f : Fin N → GeneralLinear (r + 1) F → ℂ)
    (Lq Lh : ℤ) (hL : AdjacentRankShellLowerBounds F W.val.val Φ φ Lq Lh)
    (c : ℂˣ)
    (hc : ∀ m, sliceCoefficient (⟨⟩ : LocalFieldData F) ν
      (corankOneIntegrand ψ abv U.val W'.val 0) m =
        (c : ℂ) * ∑ k ∈ Finset.Icc Lq (m - Lh), ∑ i,
          equalRankSliceCoefficient (⟨⟩ : LocalFieldData F) ν ψ W.val (B i).val φ k *
            adjacentRankMatrixSliceCoefficient F Φ χ (f i) (m - k))
    (M : Fin N → RationalFunctions)
    (hM : ∀ i, GodementJacquet.HasShiftedRationalValue qF abv
      (generalLinearHaar F r) Φ
      (fun h => (χ (determinant h) : ℂ) * f i h) (M i)) :
    AdjacentRankProductContinuationData F ψ ν W.val (fun i => (B i).val)
      U.val W'.val Φ φ χ f M c := by
  let U0 := (c : ℂ)⁻¹ • U
  have hU0 : (c : ℂ) • U0 = U := by
    simp [U0, smul_smul, c.ne_zero]
  have hc0 : ∀ m, sliceCoefficient (⟨⟩ : LocalFieldData F) ν
      (corankOneIntegrand ψ abv U0.val W'.val 0) m =
      ∑ k ∈ Finset.Icc Lq (m - Lh), ∑ i,
        equalRankSliceCoefficient (⟨⟩ : LocalFieldData F) ν ψ W.val (B i).val φ k *
          adjacentRankMatrixSliceCoefficient F Φ χ (f i) (m - k) := by
    intro m
    have he : corankOneIntegrand ψ abv U0.val W'.val 0 =
        (c : ℂ)⁻¹ • corankOneIntegrand ψ abv U.val W'.val 0 :=
      funext (corankIntegrand_smul F ψ (c : ℂ)⁻¹ U.val W'.val 0)
    rw [he, sliceCoefficient_smul, hc m, ← mul_assoc, inv_mul_cancel₀ c.ne_zero, one_mul]
  obtain ⟨A, hA, ⟨a, ha⟩, hcont, -⟩ :=
    corankOneCoefficient_productContinuation F ψ ν hν μ σ τ π hσ hτ hπ
      ℓ ℓ' ℓU hℓ hℓ' hℓU W B U0 W' Φ φ χ f Lq Lh hL.1 hL.2 hc0 M hM
  have hi (s : ℂ) : corankOneIntegral ψ abv ν U.val W'.val s =
      (c : ℂ) * corankOneIntegral ψ abv ν U0.val W'.val s := by
    rw [← hU0]
    exact corankIntegral_smul F ψ ν c U0.val W'.val s
  have hright (s : ℂ) (hs : a < s.re) :
      CorankOneConverges ψ abv ν U.val W'.val s ∧
      (∀ i, EqualRankConverges ψ abv ν W.val (B i).val φ s) ∧
      (∀ i, Langlands.AllField.GodementJacquet.Padic.MatrixConverges F Φ (s + (r : ℂ) / 2)
        (fun h => (χ (determinant h) : ℂ) * f i h)) ∧
      corankOneIntegral ψ abv ν U.val W'.val s =
        (c : ℂ) * adjacentRankFiniteProductValue F ψ ν W.val (fun i => (B i).val)
          Φ φ χ f s := by
    have h := ha s hs
    have hactual : CorankOneConverges ψ abv ν U.val W'.val s := by
      rw [← hU0]
      change Integrable (corankOneIntegrand ψ abv ((c : ℂ) • U0.val) W'.val s) ν
      have he : corankOneIntegrand ψ abv ((c : ℂ) • U0.val) W'.val s =
          fun q => (c : ℂ) * corankOneIntegrand ψ abv U0.val W'.val s q :=
        funext (corankIntegrand_smul F ψ c U0.val W'.val s)
      rw [he]
      exact h.1.const_mul c
    exact ⟨hactual, h.2.1, h.2.2.1, (hi s).trans (congrArg (fun z : ℂ => (c : ℂ) * z)
      h.2.2.2)⟩
  have hactualCont : HasRationalContinuation qF
      (fun s => corankOneIntegral ψ abv ν U.val W'.val s)
      (RatFunc.C (c : ℂ) * ∑ i, A i * M i) :=
    RationalContinuationLinear.continuation_of_eq_on_right
      (hasRationalContinuation_const_mul (c : ℂ) hcont) ⟨0, fun s _ => hi s⟩
  exact ⟨A, hA, ⟨a, hright⟩, hactualCont, fun R hR =>
    hR.unique (⟨⟩ : LocalFieldData F).residueCardinality_gt_one hactualCont⟩

set_option maxHeartbeats 2000000 in
/-- The same finite model family gives actual original and dual finite-product
identities and their unique rational continuations. All quotient analytic
inputs follow from full Whittaker type; actual matrix values are supplied. -/
theorem adjacentRankModel_matchedProductContinuation
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
        ∃ f : Fin N → GodementJacquet.biSmoothMatrixCoefficients
          (V := (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule)
          (glModelRepresentation (ψ.scale (-1)) r τ ℓ'),
          ∀ M MD : Fin N → RationalFunctions,
            (∀ i, GodementJacquet.HasShiftedRationalValue qF abv
              (generalLinearHaar F r) Φ
              (fun h => (χ (determinant h) : ℂ) * (f i).val h) (M i)) →
            (∀ i, GodementJacquet.HasShiftedRationalValue qF abv
              (generalLinearHaar F r) ΦD
              (fun h => (χ⁻¹ (determinant h) : ℂ) *
                GodementJacquet.coefficientIota (f i).val h) (MD i)) →
            AdjacentRankProductContinuationData F ψ ν W.val
              (fun i => InducedTailIntermediate.scaledStandardAsInverse ψ (B i).val)
              U.val (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val)
              Φ φ χ (fun i => (f i).val) M 1 ∧
            AdjacentRankProductContinuationData F (ψ.scale (-1)) ν WD.val
              (fun i => (dualModelLinearMap (ψ.scale (-1)) τ ℓ' (B i)).val)
              UD.val (dualModelLinearMap (ψ.scale (-1)) τ ℓ' W').val
              ΦD φHat χ⁻¹ (fun i => GodementJacquet.coefficientIota (f i).val)
              MD (adjacentRankModelStarScalar F χ r) := by
  dsimp only
  let ΦD := adjacentRankReflectedTest
    (rectangularFourierEquiv ψ μ (r + 1) (r + 1) hself Φ)
  let σD := inverseTransposePullback σ
  let πD := inverseTransposePullback π
  let τD := inverseTransposePullback τ
  let ℓD := functionalsCongr (standardCharacter_scale_neg_one ψ r).symm
    (dualFunctional ψ σ ℓ)
  let ℓUD := functionalsCongr (standardCharacter_scale_neg_one ψ (r + 1)).symm
    (dualFunctional ψ π ℓU)
  let ℓ'D := dualFunctional (ψ.scale (-1)) τ ℓ'
  let WD := inverseCoefficientAsScaledStandard F ψ σD
    (dualFunctional ψ σ ℓ) (dualModelLinearMap ψ σ ℓ W)
  let UD := inverseCoefficientAsScaledStandard F ψ πD
    (dualFunctional ψ π ℓU) (dualModelLinearMap ψ π ℓU U)
  have hτinv : IsOfWhittakerType r (inverseStandardCharacter ψ r) τ := by
    simpa only [standardCharacter_scale_neg_one] using hτ
  have hσD : IsOfWhittakerType r (standardCharacter (ψ.scale (-1)) r) σD := by
    simpa only [standardCharacter_scale_neg_one] using
      isOfWhittakerType_inverseTransposePullback ψ σ hσ
  have hπD : IsOfWhittakerType (r + 1)
      (standardCharacter (ψ.scale (-1)) (r + 1)) πD := by
    simpa only [standardCharacter_scale_neg_one] using
      isOfWhittakerType_inverseTransposePullback ψ π hπ
  have hτD : IsOfWhittakerType r
      (inverseStandardCharacter (ψ.scale (-1)) r) τD :=
    isOfWhittakerType_inverseTransposePullback (ψ.scale (-1)) τ hτ
  have hℓD : ℓD.val ≠ 0 := dualFunctional_nonzero ψ σ ℓ hℓ
  have hℓUD : ℓUD.val ≠ 0 := dualFunctional_nonzero ψ π ℓU hℓU
  have hℓ'D : ℓ'D.val ≠ 0 := dualFunctional_nonzero (ψ.scale (-1)) τ ℓ' hℓ'
  obtain ⟨Lq, Lh, LqD, LhD, N, B, hL, hLD, hB⟩ :=
    adjacentRankModel_matchedCoefficientConvolution F ψ μ hself σ hσ ℓ χ
      Φ φ φHat hφ W U.val hU τ hτ.1 ℓ' ν hν
  refine ⟨N, B, fun W' => ?_⟩
  obtain ⟨f, hco, hcd⟩ := hB W'
  refine ⟨f, fun M MD hM hMD => ⟨?_, ?_⟩⟩
  · exact corankOneCoefficient_scalarProductContinuation F ψ ν hν μ σ τ π
      hσ hτinv hπ ℓ (functionalsCongr (standardCharacter_scale_neg_one ψ r) ℓ')
      ℓU hℓ hℓ' hℓU W
      (fun i => scaledStandardCoefficientAsInverse F ψ τ ℓ' (B i))
      U (scaledStandardCoefficientAsInverse F ψ τ ℓ' W')
      Φ φ χ (fun i => (f i).val) Lq Lh hL 1 hco.2.2.2 M hM
  · exact corankOneCoefficient_scalarProductContinuation F (ψ.scale (-1)) ν hν μ
      σD τD πD hσD hτD hπD ℓD ℓ'D ℓUD hℓD hℓ'D hℓUD WD
      (fun i => dualModelLinearMap (ψ.scale (-1)) τ ℓ' (B i))
      UD (dualModelLinearMap (ψ.scale (-1)) τ ℓ' W')
      ΦD φHat χ⁻¹ (fun i => GodementJacquet.coefficientIota (f i).val)
      LqD LhD hLD (χ⁻¹ (determinant (scalar (n := r + 1) (-1 : Fˣ))))
      hcd.2.2.2 MD hMD

end Langlands.AllField.RankinSelberg.Padic
