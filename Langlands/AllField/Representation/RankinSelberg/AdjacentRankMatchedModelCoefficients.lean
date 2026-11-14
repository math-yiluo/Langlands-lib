import Langlands.Representation.RankinSelberg.AdjacentRankMatchedModelCoefficients
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankDualModelZetaCoefficient
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankSpectralExpansion
/-! Matched actual original and model-star determinant coefficients. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg.Padic hiding AdjacentRankCoefficientConvolution AdjacentRankModelConverges AdjacentRankShellConvolutionAt AdjacentRankShellLowerBounds adjacentRankBeforeShearKernel adjacentRankBeforeShearKernel_mk adjacentRankCoefficientConvolution_of_shell adjacentRankCompact_middleAverage adjacentRankCompact_middleAverage_and_dual adjacentRankDualInnerSliceIntegral adjacentRankDualMiddleAverage adjacentRankDualMiddleAverage_eq adjacentRankInnerMultiplier adjacentRankInnerMultiplier_mul adjacentRankInnerSliceWeight adjacentRankInnerSliceWeight_mul adjacentRankInnerSlice_matchedFiniteSeparation adjacentRankJointShell adjacentRankJointShellKernel adjacentRankJointShellKernel_mk adjacentRankJointShellKernel_mk_eq_innerSlice adjacentRankMatrixSliceCoefficient adjacentRankMatrixSliceExpansion adjacentRankModelConverges_of_isSmooth adjacentRankModelIntegral adjacentRankModelIntegral_mul adjacentRankModelIntegral_separated_rankInclusion_raw adjacentRankModelIntegral_separated_rankInclusion_weighted adjacentRankModelMap adjacentRankModelMapBorel adjacentRankModelMapDisconnected adjacentRankModelMapGLMeasurable adjacentRankModelMapLocalField adjacentRankModelMapMeasurable adjacentRankModelMapT2 adjacentRankModelMapTopology adjacentRankModelMapValuative adjacentRankModelMap_apply adjacentRankModelStarScalar adjacentRankModelStar_corankOneSlice_eq_before adjacentRankModelStar_separated_rankInclusion adjacentRankModelStar_separated_rankInclusion_weighted adjacentRankModel_corankOneSlice_eq_before adjacentRankModel_matchedCoefficientConvolution adjacentRankSeparatedTest_rho0_rankInclusion adjacentRankShell_finiteConvolution_of_innerSeparation adjacentRankShell_matchedFiniteConvolution adjacentRankShell_shear_fubini compactCoefficientsBorel compactCoefficientsLocalField compactCoefficientsMeasurable compactCoefficientsTopology compactCoefficientsValuativeRel continuous_adjacentRankInnerMultiplier continuous_adjacentRankInnerSliceWeight continuous_adjacentRankJointShellKernel corankOneIntegrand_eq_mul_spectralPoint_zpow corankOneSliceExpansion dualCompactFieldTopology dualCompactGroupBorel dualCompactGroupMeasurable dualCompactLocalField dualCompactValuativeRel dualModelFieldBorel dualModelFieldMeasurable dualModelFieldT2 dualModelFieldTopology dualModelFieldTotallyDisconnected dualModelGroupBorel dualModelGroupMeasurable dualModelLocalField dualModelValuativeRel dualRestrictionFieldBorel dualRestrictionFieldMeasurable dualRestrictionFieldT2 dualRestrictionFieldTopology dualRestrictionFieldTotallyDisconnected dualRestrictionGroupBorel dualRestrictionGroupMeasurable dualRestrictionLocalField dualRestrictionValuativeRel exists_adjacentRankInner_subgroup exists_matrixTest_determinantOrder_lowerBound exists_whittakerRow_determinantOrder_lowerBound hasCompactSupport_adjacentRankInnerSliceWeight hasCompactSupport_adjacentRankJointShellKernel hasCompactSupport_equalRankSlice hasSum_setIntegral_generalLinearDeterminantSlice innerSliceFieldTopology innerSliceGroupBorel innerSliceGroupMeasurable innerSliceLocalField innerSliceValuativeRel instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instTotallyDisconnectedSpaceCarrier instValuativeRelCarrier integrable_adjacentRankInnerSliceWeight_mul integrable_adjacentRankJointShellKernel integrable_equalRankSlice integral_eq_sum_determinantSlices inverseCoefficientAsScaledStandard isClopen_adjacentRankJointShell jointShellFieldT2 jointShellFieldTopology jointShellGroupBorelSpace jointShellGroupMeasurableSpace jointShellGroupSecondCountable jointShellGroupSigmaCompact jointShellLocalField jointShellQuotientBorelSpace jointShellQuotientMeasurableSpace jointShellQuotientT2 jointShellValuativeRel matchedCoefficientFieldBorel matchedCoefficientFieldMeasurable matchedCoefficientFieldT2 matchedCoefficientFieldTopology matchedCoefficientFieldTotallyDisconnected matchedCoefficientGroupBorel matchedCoefficientGroupMeasurable matchedCoefficientGroupSigmaCompact matchedCoefficientLocalField matchedCoefficientQuotientBorel matchedCoefficientQuotientMeasurable matchedCoefficientUnipotentBorel matchedCoefficientUnipotentMeasurable matchedCoefficientValuativeRel matchedInnerFieldTopology matchedInnerGroupBorel matchedInnerGroupMeasurable matchedInnerGroupSecondCountable matchedInnerGroupSigmaCompact matchedInnerLocalField matchedInnerValuativeRel matchedShellFieldT2 matchedShellFieldTopology matchedShellGroupBorel matchedShellGroupMeasurable matchedShellGroupSecondCountable matchedShellGroupSigmaCompact matchedShellLocalField matchedShellQuotientLocallyCompact matchedShellQuotientMeasurable matchedShellQuotientSecondCountable matchedShellUnipotentBorel matchedShellUnipotentMeasurable matchedShellValuativeRel modelZetaFieldBorel modelZetaFieldMeasurable modelZetaFieldT2 modelZetaFieldTopology modelZetaFieldTotallyDisconnected modelZetaGroupBorel modelZetaGroupMeasurable modelZetaLocalField modelZetaValuativeRel quotientShearFieldT2 quotientShearFieldTopology quotientShearGroupBorel quotientShearGroupMeasurable quotientShearGroupSecondCountable quotientShearGroupSigmaCompact quotientShearLocalField quotientShearQuotientBorel quotientShearQuotientLocallyCompact quotientShearQuotientMeasurable quotientShearQuotientSecondCountable quotientShearUnipotentBorel quotientShearUnipotentMeasurable quotientShearValuativeRel setIntegral_matrixIntegrand_determinantSlice shellConvolutionFieldTopology shellConvolutionLocalField shellConvolutionQuotientBorel shellConvolutionQuotientMeasurable shellConvolutionValuativeRel spectralFieldTopology spectralFieldValuation spectralGroupBorelSpace spectralGroupMeasurableSpace spectralLocalField spectralQuotientBorelSpace spectralQuotientMeasurableSpace
open Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg hiding AdjacentRankBaseModelStarIdentity AdjacentRankModelConvergenceStatement AdjacentRankModelConverges AdjacentRankModelStarStatement EqualRankAnalyticStatement EqualRankContinuedFormsStatement EqualRankFunctionalEquationStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneGammaTwistStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerRowSliceCompactSupportStatement ZeroRowLastRowCutoffStatement adjacentRankFullFourier adjacentRankFullFourier_inverseTranspose adjacentRankFullFourier_tmul adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelIntegral adjacentRankModelIntegrand adjacentRankModelStar adjacentRankModelStarBase_of_pure_integrals adjacentRankModelStarIntegrabilityLocalInstance1 adjacentRankModelStarIntegrabilityLocalInstance2 adjacentRankModelStarIntegrabilityLocalInstance3 adjacentRankModelStarIntegrabilityLocalInstance4 adjacentRankModelStarIntegrabilityLocalInstance5 adjacentRankModelStarIntegrabilityLocalInstance6 adjacentRankModelStarIntegrabilityLocalInstance7 adjacentRankModelStarIntegrabilityLocalInstance8 adjacentRankModelStarIntegrabilityLocalInstance9 adjacentRankModelStarSourceFunction_regularity adjacentRankModelStarTargetFunction_regularity adjacentRankModelStar_base adjacentRankModelStar_equality_of_base adjacentRankModelStar_pure_right_averages adjacentRankPure_hasCompactSupport adjacentRankStarEquiv adjacentRankStarEquiv_tmul_evaluation adjacentRankTransformedIntegrand adjacentRankTransformedPure_hasCompactSupport adjacentRankTransformed_integrable_of_isSmooth adjacentRank_distribHaarChar adjacentRank_fullFourier_kernel_reflected_orbit adjacentRank_fullFourier_rowTranslate adjacentRank_inverseTranspose_unipotent_epsilon adjacentRank_kernel_reflected_right_orbit adjacentRank_kernel_right_unipotent adjacentRank_partialFourier_rowTranslate adjacentRank_rho0_kernel_right_orbit continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankContinuedForms equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_iwasawa_diagonal_le_of_simpleRoot exists_schwartzBruhat_row_bound generalLinearDeterminantSlice hasCompactSupport_matrixSlice hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClopen_generalLinearDeterminantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit matrixSliceTest matrixSliceTest_apply measurableSet_determinantSlice mem_determinantSlice mem_generalLinearDeterminantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelStarBaseBorel modelStarBaseDisconnected modelStarBaseGLBorel modelStarBaseGLMeasurable modelStarBaseLocalField modelStarBaseMeasurable modelStarBaseT2 modelStarBaseTopology modelStarBaseUnipotentBorel modelStarBaseUnipotentMeasurable modelStarBaseValuative modelStarFourierBorel modelStarFourierDisconnected modelStarFourierLocalField modelStarFourierMeasurable modelStarFourierT2 modelStarFourierTopology modelStarFourierValuative modelStarOrbitFourierBorel modelStarOrbitFourierDisconnected modelStarOrbitFourierLocalField modelStarOrbitFourierMeasurable modelStarOrbitFourierSecondCountable modelStarOrbitFourierT2 modelStarOrbitFourierTopology modelStarOrbitFourierValuative modelStarReductionBorel modelStarReductionDisconnected modelStarReductionGLBorel modelStarReductionGLMeasurable modelStarReductionLocalField modelStarReductionMeasurable modelStarReductionT2 modelStarReductionTopology modelStarReductionValuative modelStarRegularityLocalField modelStarRegularityTopology modelStarRegularityValuative normalizedAbs_det_of_mem_generalLinearDeterminantSlice normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice whittakerRowSliceCompactSupport zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
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

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance matchedCoefficientFieldT2 : T2Space F :=
  (⟨⟩ : LocalFieldData F).fieldT2
local instance matchedCoefficientFieldTotallyDisconnected :
    TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance matchedCoefficientFieldMeasurable : MeasurableSpace F := borel _
local instance matchedCoefficientFieldBorel : BorelSpace F := ⟨rfl⟩
local instance matchedCoefficientGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F) := borel _
local instance matchedCoefficientGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F) := ⟨rfl⟩
local instance matchedCoefficientUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (GeneralLinear.upperUnipotent (r + 1) F) := borel _
local instance matchedCoefficientUnipotentBorel (r : ℕ) : BorelSpace
    (GeneralLinear.upperUnipotent (r + 1) F) := ⟨rfl⟩
local instance matchedCoefficientGroupSigmaCompact (r : ℕ) :
    SigmaCompactSpace (GeneralLinear (r + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSigmaCompactSpace (r + 1)
local instance matchedCoefficientQuotientMeasurable (r : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient r F) := borel _
local instance matchedCoefficientQuotientBorel (r : ℕ) :
    BorelSpace (LeftUnipotentQuotient r F) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

/-- The actual finite convolution for a supplied realized corank-one vector,
including genuine integrability of every determinant slice and factor. -/
def AdjacentRankCoefficientConvolution {r N : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    (W : WhittakerFunctions ψ r) (W' : InverseWhittakerFunctions ψ r)
    (U : WhittakerFunctions ψ (r + 1))
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (φ : SchwartzBruhat (Fin (r + 1) → F))
    (χ : Quasicharacter F)
    (ν : Measure (LeftUnipotentQuotient r F))
    (Lq Lh : ℤ) (B : Fin N → InverseWhittakerFunctions ψ r)
    (f : Fin N → GeneralLinear (r + 1) F → ℂ) (c : ℂ) : Prop :=
  SliceIntegrable (⟨⟩ : LocalFieldData F) ν (corankOneIntegrand ψ abv U W' 0) ∧
    (∀ k i, Integrable ((determinantSlice (⟨⟩ : LocalFieldData F) r k).indicator
      (equalRankIntegrand ψ abv W (B i) φ 0)) ν) ∧
    (∀ j i, Integrable (fun h => adjacentRankInnerSliceWeight F Φ χ j
      ((r : ℂ) / 2) h * f i h) (generalLinearHaar F r)) ∧
    ∀ m, sliceCoefficient (⟨⟩ : LocalFieldData F) ν
      (corankOneIntegrand ψ abv U W' 0) m =
        c * ∑ k ∈ Finset.Icc Lq (m - Lh), ∑ i,
          equalRankSliceCoefficient (⟨⟩ : LocalFieldData F) ν ψ W (B i) φ k *
            adjacentRankMatrixSliceCoefficient F Φ χ (f i) (m - k)

/-- Transfer the actual before-shell identification and a supplied outer
convolution to actual coefficients, preserving every finite witness. -/
theorem adjacentRankCoefficientConvolution_of_shell {r N : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    (W : WhittakerFunctions ψ r) (W' : InverseWhittakerFunctions ψ r)
    (U : WhittakerFunctions ψ (r + 1))
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (φ : SchwartzBruhat (Fin (r + 1) → F))
    (χ : Quasicharacter F)
    (ν : Measure (LeftUnipotentQuotient r F))
    (Lq Lh : ℤ) (B : Fin N → InverseWhittakerFunctions ψ r)
    (f : Fin N → GeneralLinear (r + 1) F → ℂ) (c : ℂ)
    (hind : ∀ m q, (determinantSlice (⟨⟩ : LocalFieldData F) r m).indicator
      (corankOneIntegrand ψ abv U W' 0) q =
        c * ∫ h, adjacentRankBeforeShearKernel F ψ W W' Φ φ
          (adjacentRankInnerMultiplier F χ ((r : ℂ) / 2)) m (q, h)
            ∂generalLinearHaar F r)
    (hshell : ∀ m, AdjacentRankShellConvolutionAt F ψ W W' Φ φ χ ν
      Lq Lh B f m ((r : ℂ) / 2)) :
    AdjacentRankCoefficientConvolution F ψ W W' U Φ φ χ ν Lq Lh B f c := by
  classical
  have he : ∀ m, (determinantSlice (⟨⟩ : LocalFieldData F) r m).indicator
      (corankOneIntegrand ψ abv U W' 0) =
        fun q => c * ∫ h, adjacentRankBeforeShearKernel F ψ W W' Φ φ
          (adjacentRankInnerMultiplier F χ ((r : ℂ) / 2)) m (q, h)
            ∂generalLinearHaar F r :=
    fun m => funext (hind m)
  have hslice : SliceIntegrable (⟨⟩ : LocalFieldData F) ν
      (corankOneIntegrand ψ abv U W' 0) := by
    intro m
    have ho := (hshell m).1.integral_prod_left
    have hi : Integrable ((determinantSlice (⟨⟩ : LocalFieldData F) r m).indicator
        (corankOneIntegrand ψ abv U W' 0)) ν := by
      rw [he m]
      exact ho.const_mul c
    exact (integrable_indicator_iff
      (measurableSet_determinantSlice (⟨⟩ : LocalFieldData F) r m)).mp hi
  refine ⟨hslice, (hshell 0).2.2.1, (hshell 0).2.2.2.1, fun m => ?_⟩
  rw [sliceCoefficient_eq_integral_indicator, he m, integral_const_mul]
  exact congrArg (fun z : ℂ => c * z) (hshell m).2.2.2.2.2

set_option maxHeartbeats 1600000 in
/-- The actual original and dual model coefficients use one finite family,
with the reflected Fourier test, inverse determinant character, and the
literal model-star scalar on the transformed side. -/
theorem adjacentRankModel_matchedCoefficientConvolution
    (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
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
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    (τ : Representation ℂ (GeneralLinear (r + 1) F) V')
    (hτ : IsAdmissible τ) (ℓ' : glFunctionals (ψ.scale (-1)) r τ)
    (ν : Measure (LeftUnipotentQuotient r F))
    (hν : IsCompatible (upperUnipotent (r + 1) F)
      (generalLinearHaar F r) (unipotentHaar F r) ν) :
    let ΦD := adjacentRankReflectedTest
      (rectangularFourierEquiv ψ μ (r + 1) (r + 1) hself Φ)
    let WD := inverseCoefficientAsScaledStandard F ψ (inverseTransposePullback σ)
      (dualFunctional ψ σ ℓ) (dualModelLinearMap ψ σ ℓ W)
    let UD := InducedTailIntermediate.inverseAsScaledStandard ψ
      (dualFunctionEquiv ψ (r + 1) U)
    ∃ (Lq Lh LqD LhD : ℤ) (N : ℕ)
      (B : Fin N → (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule),
      AdjacentRankShellLowerBounds F W.val.val Φ φ Lq Lh ∧
      AdjacentRankShellLowerBounds F WD.val.val ΦD φHat LqD LhD ∧
      ∀ W' : (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule,
        ∃ f : Fin N → GodementJacquet.biSmoothMatrixCoefficients
          (V := (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule)
          (glModelRepresentation (ψ.scale (-1)) r τ ℓ'),
          AdjacentRankCoefficientConvolution F ψ W.val
            (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val)
            U Φ φ χ ν Lq Lh
            (fun i => InducedTailIntermediate.scaledStandardAsInverse ψ (B i).val)
            (fun i => (f i).val) 1 ∧
          AdjacentRankCoefficientConvolution F (ψ.scale (-1)) WD.val
            (dualModelLinearMap (ψ.scale (-1)) τ ℓ' W').val
            UD ΦD φHat χ⁻¹ ν LqD LhD
            (fun i => (dualModelLinearMap (ψ.scale (-1)) τ ℓ' (B i)).val)
            (fun i => GodementJacquet.coefficientIota (f i).val)
            (adjacentRankModelStarScalar F χ r) := by
  dsimp only
  let ΦD := adjacentRankReflectedTest
    (rectangularFourierEquiv ψ μ (r + 1) (r + 1) hself Φ)
  let WD := inverseCoefficientAsScaledStandard F ψ (inverseTransposePullback σ)
    (dualFunctional ψ σ ℓ) (dualModelLinearMap ψ σ ℓ W)
  let UD := InducedTailIntermediate.inverseAsScaledStandard ψ
    (dualFunctionEquiv ψ (r + 1) U)
  obtain ⟨Lq, Lh, LqD, LhD, N, B, hL, hLD, hB⟩ :=
    adjacentRankShell_matchedFiniteConvolution F ψ σ hσ.1.1 ℓ W τ hτ ℓ'
      Φ ΦD φ φHat χ χ⁻¹ ν hν
  refine ⟨Lq, Lh, LqD, LhD, N, B, hL, hLD, fun W' => ?_⟩
  obtain ⟨f, hf⟩ := hB W'
  refine ⟨f, ?_, ?_⟩
  · apply adjacentRankCoefficientConvolution_of_shell F ψ W.val
      (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val) U Φ φ χ ν
      Lq Lh (fun i => InducedTailIntermediate.scaledStandardAsInverse ψ (B i).val)
      (fun i => (f i).val) 1
    · intro m q
      simpa only [one_mul] using adjacentRankModel_corankOneSlice_eq_before
        F ψ μ hself σ ℓ χ Φ φ W U hU
        (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val) m q
    · exact fun m => (hf m ((r : ℂ) / 2)).1
  · apply adjacentRankCoefficientConvolution_of_shell F (ψ.scale (-1)) WD.val
      (dualModelLinearMap (ψ.scale (-1)) τ ℓ' W').val UD ΦD φHat χ⁻¹ ν
      LqD LhD (fun i => (dualModelLinearMap (ψ.scale (-1)) τ ℓ' (B i)).val)
      (fun i => GodementJacquet.coefficientIota (f i).val)
      (adjacentRankModelStarScalar F χ r)
    · exact fun m q => adjacentRankModelStar_corankOneSlice_eq_before
        F ψ μ hself σ hσ ℓ χ Φ φ φHat hφ W U hU
        (dualModelLinearMap (ψ.scale (-1)) τ ℓ' W').val m q
    · exact fun m => (hf m ((r : ℂ) / 2)).2

end Langlands.AllField.RankinSelberg.Padic
