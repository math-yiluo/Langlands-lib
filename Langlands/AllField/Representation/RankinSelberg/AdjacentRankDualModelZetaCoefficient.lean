import Langlands.Representation.RankinSelberg.AdjacentRankDualModelZetaCoefficient
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankDualRestriction
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankMatchedShellConvolution
/-! The literal model-star restriction and the matched determinant coefficients. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding AdjacentRankBaseModelStarIdentity AdjacentRankModelConvergenceStatement AdjacentRankModelStarStatement EqualRankAnalyticStatement EqualRankContinuedFormsStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneGammaTwistStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerRowSliceCompactSupportStatement ZeroRowLastRowCutoffStatement adjacentRankFullFourier adjacentRankFullFourier_inverseTranspose adjacentRankFullFourier_tmul adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelStar adjacentRankModelStarBase_of_pure_integrals adjacentRankModelStarIntegrabilityLocalInstance1 adjacentRankModelStarIntegrabilityLocalInstance2 adjacentRankModelStarIntegrabilityLocalInstance3 adjacentRankModelStarIntegrabilityLocalInstance4 adjacentRankModelStarIntegrabilityLocalInstance5 adjacentRankModelStarIntegrabilityLocalInstance6 adjacentRankModelStarIntegrabilityLocalInstance7 adjacentRankModelStarIntegrabilityLocalInstance8 adjacentRankModelStarIntegrabilityLocalInstance9 adjacentRankModelStarSourceFunction_regularity adjacentRankModelStarTargetFunction_regularity adjacentRankModelStar_base adjacentRankModelStar_equality_of_base adjacentRankModelStar_pure_right_averages adjacentRankPure_hasCompactSupport adjacentRankTransformedIntegrand adjacentRankTransformedPure_hasCompactSupport adjacentRankTransformed_integrable_of_isSmooth adjacentRank_distribHaarChar adjacentRank_fullFourier_kernel_reflected_orbit adjacentRank_fullFourier_rowTranslate adjacentRank_inverseTranspose_unipotent_epsilon adjacentRank_kernel_reflected_right_orbit adjacentRank_kernel_right_unipotent adjacentRank_partialFourier_rowTranslate adjacentRank_rho0_kernel_right_orbit continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankContinuedForms equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_iwasawa_diagonal_le_of_simpleRoot exists_schwartzBruhat_row_bound generalLinearDeterminantSlice hasCompactSupport_matrixSlice iUnion_determinantSlice isClopen_determinantSlice isClopen_generalLinearDeterminantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit matrixSliceTest matrixSliceTest_apply measurableSet_determinantSlice mem_determinantSlice mem_generalLinearDeterminantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelStarBaseBorel modelStarBaseDisconnected modelStarBaseGLBorel modelStarBaseGLMeasurable modelStarBaseLocalField modelStarBaseMeasurable modelStarBaseT2 modelStarBaseTopology modelStarBaseUnipotentBorel modelStarBaseUnipotentMeasurable modelStarBaseValuative modelStarFourierBorel modelStarFourierDisconnected modelStarFourierLocalField modelStarFourierMeasurable modelStarFourierT2 modelStarFourierTopology modelStarFourierValuative modelStarOrbitFourierBorel modelStarOrbitFourierDisconnected modelStarOrbitFourierLocalField modelStarOrbitFourierMeasurable modelStarOrbitFourierSecondCountable modelStarOrbitFourierT2 modelStarOrbitFourierTopology modelStarOrbitFourierValuative modelStarReductionBorel modelStarReductionDisconnected modelStarReductionGLBorel modelStarReductionGLMeasurable modelStarReductionLocalField modelStarReductionMeasurable modelStarReductionT2 modelStarReductionTopology modelStarReductionValuative modelStarRegularityLocalField modelStarRegularityTopology modelStarRegularityValuative normalizedAbs_det_of_mem_generalLinearDeterminantSlice normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable whittakerRowSliceCompactSupport zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding AdjacentRankUnipotentFourierStatement PadicMatrixFourierSliceStatement PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement adjacentRankUnipotentFourier padicMatrixFourierSlice padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierEquivariance padicScalarHaarScaling padicUnipotentHaar_iota_fourier_duality_right
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.QuotientIntegration
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open scoped BigOperators

universe uF uV uW

namespace Padic
open Langlands.RankinSelberg.Padic hiding AdjacentRankModelConverges AdjacentRankShellConvolutionAt AdjacentRankShellLowerBounds adjacentRankBeforeShearKernel adjacentRankBeforeShearKernel_mk adjacentRankCompact_middleAverage adjacentRankCompact_middleAverage_and_dual adjacentRankDualInnerSliceIntegral adjacentRankDualMiddleAverage adjacentRankDualMiddleAverage_eq adjacentRankInnerMultiplier adjacentRankInnerMultiplier_mul adjacentRankInnerSliceWeight adjacentRankInnerSliceWeight_mul adjacentRankInnerSlice_matchedFiniteSeparation adjacentRankJointShell adjacentRankJointShellKernel adjacentRankJointShellKernel_mk adjacentRankJointShellKernel_mk_eq_innerSlice adjacentRankModelConverges_of_isSmooth adjacentRankModelIntegral adjacentRankModelIntegral_mul adjacentRankModelIntegral_separated_rankInclusion_raw adjacentRankModelIntegral_separated_rankInclusion_weighted adjacentRankModelMap adjacentRankModelMapBorel adjacentRankModelMapDisconnected adjacentRankModelMapGLMeasurable adjacentRankModelMapLocalField adjacentRankModelMapMeasurable adjacentRankModelMapT2 adjacentRankModelMapTopology adjacentRankModelMapValuative adjacentRankModelMap_apply adjacentRankModelStarScalar adjacentRankModelStar_corankOneSlice_eq_before adjacentRankModelStar_separated_rankInclusion adjacentRankModelStar_separated_rankInclusion_weighted adjacentRankModel_corankOneSlice_eq_before adjacentRankSeparatedTest_rho0_rankInclusion adjacentRankShell_finiteConvolution_of_innerSeparation adjacentRankShell_matchedFiniteConvolution adjacentRankShell_shear_fubini compactCoefficientsBorel compactCoefficientsLocalField compactCoefficientsMeasurable compactCoefficientsTopology compactCoefficientsValuativeRel continuous_adjacentRankInnerMultiplier continuous_adjacentRankInnerSliceWeight continuous_adjacentRankJointShellKernel dualCompactFieldTopology dualCompactGroupBorel dualCompactGroupMeasurable dualCompactLocalField dualCompactValuativeRel dualModelFieldBorel dualModelFieldMeasurable dualModelFieldT2 dualModelFieldTopology dualModelFieldTotallyDisconnected dualModelGroupBorel dualModelGroupMeasurable dualModelLocalField dualModelValuativeRel dualRestrictionFieldBorel dualRestrictionFieldMeasurable dualRestrictionFieldT2 dualRestrictionFieldTopology dualRestrictionFieldTotallyDisconnected dualRestrictionGroupBorel dualRestrictionGroupMeasurable dualRestrictionLocalField dualRestrictionValuativeRel exists_adjacentRankInner_subgroup exists_matrixTest_determinantOrder_lowerBound exists_whittakerRow_determinantOrder_lowerBound hasCompactSupport_adjacentRankInnerSliceWeight hasCompactSupport_adjacentRankJointShellKernel hasCompactSupport_equalRankSlice innerSliceFieldTopology innerSliceGroupBorel innerSliceGroupMeasurable innerSliceLocalField innerSliceValuativeRel instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instTotallyDisconnectedSpaceCarrier instValuativeRelCarrier integrable_adjacentRankInnerSliceWeight_mul integrable_adjacentRankJointShellKernel integrable_equalRankSlice integral_eq_sum_determinantSlices inverseCoefficientAsScaledStandard isClopen_adjacentRankJointShell jointShellFieldT2 jointShellFieldTopology jointShellGroupBorelSpace jointShellGroupMeasurableSpace jointShellGroupSecondCountable jointShellGroupSigmaCompact jointShellLocalField jointShellQuotientBorelSpace jointShellQuotientMeasurableSpace jointShellQuotientT2 jointShellValuativeRel matchedInnerFieldTopology matchedInnerGroupBorel matchedInnerGroupMeasurable matchedInnerGroupSecondCountable matchedInnerGroupSigmaCompact matchedInnerLocalField matchedInnerValuativeRel matchedShellFieldT2 matchedShellFieldTopology matchedShellGroupBorel matchedShellGroupMeasurable matchedShellGroupSecondCountable matchedShellGroupSigmaCompact matchedShellLocalField matchedShellQuotientLocallyCompact matchedShellQuotientMeasurable matchedShellQuotientSecondCountable matchedShellUnipotentBorel matchedShellUnipotentMeasurable matchedShellValuativeRel modelZetaFieldBorel modelZetaFieldMeasurable modelZetaFieldT2 modelZetaFieldTopology modelZetaFieldTotallyDisconnected modelZetaGroupBorel modelZetaGroupMeasurable modelZetaLocalField modelZetaValuativeRel quotientShearFieldT2 quotientShearFieldTopology quotientShearGroupBorel quotientShearGroupMeasurable quotientShearGroupSecondCountable quotientShearGroupSigmaCompact quotientShearLocalField quotientShearQuotientBorel quotientShearQuotientLocallyCompact quotientShearQuotientMeasurable quotientShearQuotientSecondCountable quotientShearUnipotentBorel quotientShearUnipotentMeasurable quotientShearValuativeRel shellConvolutionFieldTopology shellConvolutionLocalField shellConvolutionQuotientBorel shellConvolutionQuotientMeasurable shellConvolutionValuativeRel
open Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg hiding AdjacentRankBaseModelStarIdentity AdjacentRankModelConvergenceStatement AdjacentRankModelConverges AdjacentRankModelStarStatement EqualRankAnalyticStatement EqualRankContinuedFormsStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneGammaTwistStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerRowSliceCompactSupportStatement ZeroRowLastRowCutoffStatement adjacentRankFullFourier adjacentRankFullFourier_inverseTranspose adjacentRankFullFourier_tmul adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelIntegral adjacentRankModelIntegrand adjacentRankModelStar adjacentRankModelStarBase_of_pure_integrals adjacentRankModelStarIntegrabilityLocalInstance1 adjacentRankModelStarIntegrabilityLocalInstance2 adjacentRankModelStarIntegrabilityLocalInstance3 adjacentRankModelStarIntegrabilityLocalInstance4 adjacentRankModelStarIntegrabilityLocalInstance5 adjacentRankModelStarIntegrabilityLocalInstance6 adjacentRankModelStarIntegrabilityLocalInstance7 adjacentRankModelStarIntegrabilityLocalInstance8 adjacentRankModelStarIntegrabilityLocalInstance9 adjacentRankModelStarSourceFunction_regularity adjacentRankModelStarTargetFunction_regularity adjacentRankModelStar_base adjacentRankModelStar_equality_of_base adjacentRankModelStar_pure_right_averages adjacentRankPure_hasCompactSupport adjacentRankStarEquiv adjacentRankStarEquiv_tmul_evaluation adjacentRankTransformedIntegrand adjacentRankTransformedPure_hasCompactSupport adjacentRankTransformed_integrable_of_isSmooth adjacentRank_distribHaarChar adjacentRank_fullFourier_kernel_reflected_orbit adjacentRank_fullFourier_rowTranslate adjacentRank_inverseTranspose_unipotent_epsilon adjacentRank_kernel_reflected_right_orbit adjacentRank_kernel_right_unipotent adjacentRank_partialFourier_rowTranslate adjacentRank_rho0_kernel_right_orbit continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankContinuedForms equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_iwasawa_diagonal_le_of_simpleRoot exists_schwartzBruhat_row_bound generalLinearDeterminantSlice hasCompactSupport_matrixSlice iUnion_determinantSlice isClopen_determinantSlice isClopen_generalLinearDeterminantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit matrixSliceTest matrixSliceTest_apply measurableSet_determinantSlice mem_determinantSlice mem_generalLinearDeterminantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelStarBaseBorel modelStarBaseDisconnected modelStarBaseGLBorel modelStarBaseGLMeasurable modelStarBaseLocalField modelStarBaseMeasurable modelStarBaseT2 modelStarBaseTopology modelStarBaseUnipotentBorel modelStarBaseUnipotentMeasurable modelStarBaseValuative modelStarFourierBorel modelStarFourierDisconnected modelStarFourierLocalField modelStarFourierMeasurable modelStarFourierT2 modelStarFourierTopology modelStarFourierValuative modelStarOrbitFourierBorel modelStarOrbitFourierDisconnected modelStarOrbitFourierLocalField modelStarOrbitFourierMeasurable modelStarOrbitFourierSecondCountable modelStarOrbitFourierT2 modelStarOrbitFourierTopology modelStarOrbitFourierValuative modelStarReductionBorel modelStarReductionDisconnected modelStarReductionGLBorel modelStarReductionGLMeasurable modelStarReductionLocalField modelStarReductionMeasurable modelStarReductionT2 modelStarReductionTopology modelStarReductionValuative modelStarRegularityLocalField modelStarRegularityTopology modelStarRegularityValuative normalizedAbs_det_of_mem_generalLinearDeterminantSlice normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable whittakerRowSliceCompactSupport zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance dualModelFieldT2 : T2Space F :=
  (⟨⟩ : LocalFieldData F).fieldT2
local instance dualModelFieldTotallyDisconnected : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance dualModelFieldMeasurable : MeasurableSpace F := borel _
local instance dualModelFieldBorel : BorelSpace F := ⟨rfl⟩
local instance dualModelGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F) := borel _
local instance dualModelGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

/-- The literal character scalar from the model-star sign matrix. -/
def adjacentRankModelStarScalar (χ : Quasicharacter F) (r : ℕ) : ℂ :=
  χ⁻¹ (determinant (scalar (n := r + 1) (-1 : Fˣ)))

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

set_option maxHeartbeats 1600000 in
/-- Right translation of the literal fixed-character model-star restriction
gives exactly the reflected before-shell integrand and its sign scalar. -/
theorem adjacentRankModelStar_separated_rankInclusion_weighted
    (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
    (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F)
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (φ φHat : SchwartzBruhat (Fin (r + 1) → F))
    (hφ : IsRowFourierPair ψ μ φ φHat)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (g : GeneralLinear (r + 1) F) (s : ℂ) :
    let ΦD := adjacentRankReflectedTest
      (rectangularFourierEquiv ψ μ (r + 1) (r + 1) hself Φ)
    let WD := inverseCoefficientAsScaledStandard F ψ (inverseTransposePullback σ)
      (dualFunctional ψ σ ℓ) (dualModelLinearMap ψ σ ℓ W)
    adjacentRankModelIntegral F ψ μ hself σ ℓ χ
        (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W)
        (weylLong (r + 2) F *
          inverseTranspose (r + 2) F (rankInclusion 1 g)) *
        determinantWeight abv g (s - 1 / 2) =
      adjacentRankModelStarScalar F χ r * determinantWeight abv g s *
        ∫ h, ΦD h.val * φHat (lastRow (g * h⁻¹)) * WD.val.val (g * h⁻¹) *
          adjacentRankInnerMultiplier F χ⁻¹ ((r : ℂ) / 2) h
            ∂generalLinearHaar F r := by
  dsimp only
  let ΦHat := rectangularFourierEquiv ψ μ (r + 1) (r + 1) hself Φ
  let ΦD := adjacentRankReflectedTest ΦHat
  let WD := inverseCoefficientAsScaledStandard F ψ (inverseTransposePullback σ)
    (dualFunctional ψ σ ℓ) (dualModelLinearMap ψ σ ℓ W)
  let c := scalar (n := r + 1) (-1 : Fˣ)
  let a := adjacentRankInnerMultiplier F (r := r) χ⁻¹ ((r : ℂ) / 2)
  let orig := fun h : GeneralLinear (r + 1) F =>
    ΦD (h * g).val * φHat (lastRow h⁻¹) * WD.val.val h⁻¹ * a h
  let after := fun h : GeneralLinear (r + 1) F =>
    ΦD h.val * φHat (lastRow (g * h⁻¹)) * WD.val.val (g * h⁻¹) * a h
  have he : ∀ h, after (h * g) = a g * orig h := by
    intro h
    dsimp only [after, orig, a]
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul,
      adjacentRankInnerMultiplier_mul]
    ring
  have hi : (∫ h, after h ∂generalLinearHaar F r) =
      a g * ∫ h, orig h ∂generalLinearHaar F r := by
    rw [← integral_mul_right_eq_self after g]
    simp_rw [he]
    exact integral_const_mul _ _
  have hraw := (adjacentRankModelStar_separated_rankInclusion
    F ψ μ hself σ hσ ℓ χ Φ φ φHat hφ W g).2.2
  have hk : adjacentRankZeta F r * rankInclusion 1 g =
      rankInclusion 1 (c * g) := by
    rw [adjacentRankZeta_eq_rankInclusion, map_mul]
  have hdet : determinant (adjacentRankZeta F r * rankInclusion 1 g) =
      determinant (c * g) := by
    rw [hk]
    exact Units.ext (det_rankInclusion 1 (c * g))
  have hwc (t : ℂ) : determinantWeight abv c t = 1 := by
    simp [determinantWeight, c, scalar]
  have hwk (t : ℂ) :
      determinantWeight abv (adjacentRankZeta F r * rankInclusion 1 g) t =
        determinantWeight abv g t := by
    rw [hk]
    change (abv (Matrix.det (rankInclusion 1 (c * g)).val) : ℂ) ^ t = _
    rw [det_rankInclusion]
    change determinantWeight abv (c * g) t = _
    rw [determinantWeight_mul, hwc, one_mul]
  have hJ :
      (fun h : GeneralLinear (r + 1) F =>
        ΦHat (h * (c * g)).val * φHat (lastRow h⁻¹) *
          W.val.val (weylLong (r + 1) F *
            inverseTranspose (r + 1) F h⁻¹) *
          (χ⁻¹ (determinant h) : ℂ) * determinantWeight abv h ((r : ℂ) / 2)) =
        orig := by
    funext h
    rw [← adjacentRankReflectedTest_mul]
    change ΦD (h * g).val * φHat (lastRow h⁻¹) * WD.val.val h⁻¹ *
      (χ⁻¹ (determinant h) : ℂ) * determinantWeight abv h ((r : ℂ) / 2) = _
    dsimp only [orig, a, adjacentRankInnerMultiplier]
    ring
  change _ = (χ⁻¹ (determinant
      (adjacentRankZeta F r * rankInclusion 1 g)) : ℂ) *
    determinantWeight abv (adjacentRankZeta F r * rankInclusion 1 g)
      (((r + 1 : ℕ) : ℂ) / 2) *
    ∫ h, ΦHat (h * (c * g)).val * φHat (lastRow h⁻¹) *
      W.val.val (weylLong (r + 1) F *
        inverseTranspose (r + 1) F h⁻¹) *
      (χ⁻¹ (determinant h) : ℂ) * determinantWeight abv h ((r : ℂ) / 2)
        ∂generalLinearHaar F r at hraw
  rw [hJ, hdet, hwk, map_mul, map_mul, Units.val_mul] at hraw
  have hw : (χ⁻¹ (determinant g) : ℂ) *
      determinantWeight abv g (((r + 1 : ℕ) : ℂ) / 2) *
      determinantWeight abv g (s - 1 / 2) =
        determinantWeight abv g s * a g := by
    dsimp only [a, adjacentRankInnerMultiplier]
    rw [mul_assoc, ← determinantWeight_exponent_add, mul_left_comm,
      ← determinantWeight_exponent_add]
    congr 2
    push_cast
    ring
  rw [hraw]
  change (((χ⁻¹ (determinant c) : ℂ) * (χ⁻¹ (determinant g) : ℂ) *
    determinantWeight abv g (((r + 1 : ℕ) : ℂ) / 2) *
      (∫ h, orig h ∂generalLinearHaar F r)) *
        determinantWeight abv g (s - 1 / 2)) =
    adjacentRankModelStarScalar F χ r * determinantWeight abv g s *
      ∫ h, after h ∂generalLinearHaar F r
  rw [hi]
  calc
    _ = (χ⁻¹ (determinant c) : ℂ) *
        ((χ⁻¹ (determinant g) : ℂ) *
          determinantWeight abv g (((r + 1 : ℕ) : ℂ) / 2) *
          determinantWeight abv g (s - 1 / 2)) *
        (∫ h, orig h ∂generalLinearHaar F r) := by ring
    _ = _ := by
      rw [hw]
      dsimp only [adjacentRankModelStarScalar, c]
      ring

set_option maxHeartbeats 1600000 in
/-- The actual dual corank-one determinant indicator is the matched
before-shell integral times the explicit model-star scalar. -/
theorem adjacentRankModelStar_corankOneSlice_eq_before
    (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
    (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F)
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (φ φHat : SchwartzBruhat (Fin (r + 1) → F))
    (hφ : IsRowFourierPair ψ μ φ φHat)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (U : WhittakerFunctions ψ (r + 1))
    (hU : ∀ g, U.val g = adjacentRankModelIntegral F ψ μ hself σ ℓ χ
      (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W) g)
    (W'D : InverseWhittakerFunctions (ψ.scale (-1)) r) (m : ℤ)
    (q : LeftUnipotentQuotient r F) :
    let ΦD := adjacentRankReflectedTest
      (rectangularFourierEquiv ψ μ (r + 1) (r + 1) hself Φ)
    let WD := inverseCoefficientAsScaledStandard F ψ (inverseTransposePullback σ)
      (dualFunctional ψ σ ℓ) (dualModelLinearMap ψ σ ℓ W)
    let UD := InducedTailIntermediate.inverseAsScaledStandard ψ
      (dualFunctionEquiv ψ (r + 1) U)
    (determinantSlice (⟨⟩ : LocalFieldData F) r m).indicator
        (corankOneIntegrand (ψ.scale (-1)) abv UD W'D 0) q =
      adjacentRankModelStarScalar F χ r *
        ∫ h, adjacentRankBeforeShearKernel F (ψ.scale (-1)) WD.val W'D ΦD φHat
          (adjacentRankInnerMultiplier F χ⁻¹ ((r : ℂ) / 2)) m (q, h)
            ∂generalLinearHaar F r := by
  classical
  dsimp only
  induction q using Quotient.inductionOn with
  | h g =>
    by_cases hg : (⟨⟩ : LocalFieldData F).ord (determinant g : F) = m
    · rw [Set.indicator_of_mem (show Quotient.mk _ g ∈
        determinantSlice (⟨⟩ : LocalFieldData F) r m from hg),
        corankOneIntegrand_mk]
      change U.val (weylLong (r + 2) F *
        inverseTranspose (r + 2) F (rankInclusion 1 g)) *
        W'D.val g * determinantWeight abv g (0 - 1 / 2) = _
      rw [hU]
      have hw := adjacentRankModelStar_separated_rankInclusion_weighted
        F ψ μ hself σ hσ ℓ χ Φ φ φHat hφ W g 0
      dsimp only at hw
      simp only [determinantWeight_zero, mul_one] at hw
      calc
        _ = (adjacentRankModelIntegral F ψ μ hself σ ℓ χ
              (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W)
              (weylLong (r + 2) F *
                inverseTranspose (r + 2) F (rankInclusion 1 g)) *
              determinantWeight abv g (0 - 1 / 2)) * W'D.val g := by ring
        _ = _ := by
          rw [hw]
          rw [mul_assoc, ← integral_mul_const]
          congr 1
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun h => by
            dsimp only
            rw [adjacentRankBeforeShearKernel_mk, ite_eq_left hg]
            ring
    · rw [Set.indicator_of_notMem (show Quotient.mk _ g ∉
        determinantSlice (⟨⟩ : LocalFieldData F) r m from hg)]
      simp only [adjacentRankBeforeShearKernel_mk, ite_eq_right hg,
        integral_zero, mul_zero]

end Padic
end Langlands.AllField.RankinSelberg
