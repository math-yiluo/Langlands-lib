import Langlands.Representation.RankinSelberg.AdjacentRankProductContinuation
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankFiniteProducts
import Langlands.AllField.Representation.RankinSelberg.EqualRankAnalyticProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankAnalyticProof
/-! Actual coefficient-model convergence and continuation of the finite products. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg.Padic hiding AdjacentRankModelConverges adjacentRankBeforeShearKernel adjacentRankBeforeShearKernel_mk adjacentRankCompact_middleAverage adjacentRankFiniteProductValue adjacentRankInnerMultiplier adjacentRankInnerMultiplier_mul adjacentRankInnerSliceWeight adjacentRankInnerSliceWeight_mul adjacentRankJointShell adjacentRankJointShellKernel adjacentRankJointShellKernel_mk adjacentRankJointShellKernel_mk_eq_innerSlice adjacentRankMatrixSliceCoefficient adjacentRankMatrixSliceCoefficient_eq_zero_of_pointwise_bound adjacentRankMatrixSliceExpansion adjacentRankModelIntegral adjacentRankModelIntegral_separated_rankInclusion_raw adjacentRankModelIntegral_separated_rankInclusion_weighted adjacentRankModel_corankOneSlice_eq_before adjacentRankSeparatedTest_rho0_rankInclusion adjacentRankShell_shear_fubini compactCoefficientsBorel compactCoefficientsLocalField compactCoefficientsMeasurable compactCoefficientsTopology compactCoefficientsValuativeRel continuationFieldMeasurableSpace continuationFieldTopology continuationFieldValuation continuationGroupBorelSpace continuationGroupMeasurableSpace continuationLocalField continuationQuotientMeasurableSpace continuationUnipotentBorelSpace continuationUnipotentMeasurableSpace continuous_adjacentRankInnerMultiplier continuous_adjacentRankInnerSliceWeight continuous_adjacentRankJointShellKernel corankOneCoefficient_convergesOnRight corankOneCoefficient_productContinuation corankOneIntegral_eq_finiteProducts_of_coefficients corankOneIntegrand_eq_mul_spectralPoint_zpow corankOneSliceExpansion equalRankSliceCoefficient_eq_zero_of_pointwise_bound exists_adjacentRankInner_subgroup exists_matrixTest_determinantOrder_lowerBound exists_whittakerRow_determinantOrder_lowerBound hasCompactSupport_adjacentRankInnerSliceWeight hasCompactSupport_adjacentRankJointShellKernel hasCompactSupport_equalRankSlice hasSum_setIntegral_generalLinearDeterminantSlice innerSliceFieldTopology innerSliceGroupBorel innerSliceGroupMeasurable innerSliceLocalField innerSliceValuativeRel instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instTotallyDisconnectedSpaceCarrier instValuativeRelCarrier integrable_adjacentRankInnerSliceWeight_mul integrable_adjacentRankJointShellKernel integrable_equalRankSlice integral_eq_sum_determinantSlices isClopen_adjacentRankJointShell jointShellFieldT2 jointShellFieldTopology jointShellGroupBorelSpace jointShellGroupMeasurableSpace jointShellGroupSecondCountable jointShellGroupSigmaCompact jointShellLocalField jointShellQuotientBorelSpace jointShellQuotientMeasurableSpace jointShellQuotientT2 jointShellValuativeRel modelZetaFieldBorel modelZetaFieldMeasurable modelZetaFieldT2 modelZetaFieldTopology modelZetaFieldTotallyDisconnected modelZetaGroupBorel modelZetaGroupMeasurable modelZetaLocalField modelZetaValuativeRel productsFieldTopology productsQuotientMeasurableSpace quotientShearFieldT2 quotientShearFieldTopology quotientShearGroupBorel quotientShearGroupMeasurable quotientShearGroupSecondCountable quotientShearGroupSigmaCompact quotientShearLocalField quotientShearQuotientBorel quotientShearQuotientLocallyCompact quotientShearQuotientMeasurable quotientShearQuotientSecondCountable quotientShearUnipotentBorel quotientShearUnipotentMeasurable quotientShearValuativeRel scaledStandardCoefficientAsInverse setIntegral_matrixIntegrand_determinantSlice shellConvolutionFieldTopology shellConvolutionLocalField shellConvolutionQuotientBorel shellConvolutionQuotientMeasurable shellConvolutionValuativeRel spectralFieldTopology spectralFieldValuation spectralGroupBorelSpace spectralGroupMeasurableSpace spectralLocalField spectralQuotientBorelSpace spectralQuotientMeasurableSpace
open Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement AdjacentRankModelConverges EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankFunctionalEquationStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement EqualRankUnitValueStatement FiniteFunctionMellinStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RootTorusProductStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerRowSliceCompactSupportStatement ZeroRowLastRowCutoffStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelIntegral adjacentRankModelIntegrand adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankAnalytic equalRankCompactRootExpansion equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankNormalizedCompactIntegration equalRankQuotientAnalytic equalRankRootAverageAnalytic equalRankRootExpansion equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport equalRankUnitValue exists_adjacentRank_lastColumn_bound exists_iwasawa_diagonal_le_of_simpleRoot exists_schwartzBruhat_row_bound finiteFunctionMellin finiteFunctionShellSeries generalLinearDeterminantSlice hasCompactSupport_matrixSlice hasEqualRankCompactTest_of_kirillov hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClopen_generalLinearDeterminantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice iwasawaTorusSum lastRowCompactOrbit matrixSliceTest matrixSliceTest_apply measurableSet_determinantSlice mem_determinantSlice mem_generalLinearDeterminantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbs_det_of_mem_generalLinearDeterminantSlice normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow oneVariableMellin pairwise_disjoint_determinantSlice quotientIwasawaIntegration quotientRootIntegration rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice unequalRankAnalytic unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIwasawaSupport unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion whittakerRowSliceCompactSupport zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement padicMatrixFourierSlice padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement exists_compactOpen_glCoefficientRightStabilizer mirabolicUnitTest modelKirillovTransfer smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.QuotientIntegration
open scoped BigOperators

universe uF uV uW uU

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance continuationFieldMeasurableSpace : MeasurableSpace F := borel _
local instance continuationGroupMeasurableSpace (r : ℕ) : MeasurableSpace
    (Langlands.GeneralLinear (r + 1) F) := borel _
local instance continuationGroupBorelSpace (r : ℕ) : BorelSpace
    (Langlands.GeneralLinear (r + 1) F) := ⟨rfl⟩
local instance continuationUnipotentMeasurableSpace (r : ℕ) : MeasurableSpace
    (GeneralLinear.upperUnipotent (r + 1) F) := borel _
local instance continuationUnipotentBorelSpace (r : ℕ) : BorelSpace
    (GeneralLinear.upperUnipotent (r + 1) F) := ⟨rfl⟩
local instance continuationQuotientMeasurableSpace (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F) := borel _

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)
local notation "qF" => (Langlands.LocalFieldData.residueCardinality (⟨⟩ : LocalFieldData F))

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
  {VU : Type uU} [AddCommGroup VU] [Module ℂ VU]

set_option maxHeartbeats 800000 in
/-- Recast a vector in the actual scaled-character coefficient image as a vector
in the inverse-character image of the same transported functional. -/
def scaledStandardCoefficientAsInverse
    (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V')
    (ℓ' : glFunctionals (ψ.scale (-1)) r τ)
    (W' : (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule) :
    (coefficientModel τ
      (functionalsCongr (standardCharacter_scale_neg_one ψ r) ℓ')).toSubmodule :=
  ⟨InducedTailIntermediate.scaledStandardAsInverse ψ W'.val, by
    obtain ⟨v, hv⟩ := W'.property
    refine ⟨v, Subtype.ext ?_⟩
    exact congrArg (fun w : WhittakerFunctions (ψ.scale (-1)) r => w.val) hv⟩

/-- The zero-row analytic theorem supplies actual corank-one convergence for
coefficient vectors of full Whittaker-type representations. -/
theorem corankOneCoefficient_convergesOnRight
    (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
    [Measure.IsMulRightInvariant (unipotentHaar F r)]
    (ν : Measure (LeftUnipotentQuotient r F))
    (hν : IsCompatible (GeneralLinear.upperUnipotent (r + 1) F)
      (generalLinearHaar F r) (unipotentHaar F r) ν)
    (μ : AdditiveHaarMeasure F)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1 + 1) F) VU)
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V')
    (hπ : IsOfWhittakerType (r + 1) (standardCharacter ψ (r + 1)) π)
    (hτ : IsOfWhittakerType r (inverseStandardCharacter ψ r) τ)
    (ℓU : glFunctionals ψ (r + 1) π) (ℓ' : glInverseFunctionals ψ r τ)
    (hℓU : ℓU.val ≠ 0) (hℓ' : ℓ'.val ≠ 0)
    (U : (glCoefficientModel ψ (r + 1) π ℓU).toSubmodule)
    (W' : (coefficientModel τ ℓ').toSubmodule) :
    ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      CorankOneConverges ψ abv ν U.val W'.val s := by
  have han := unequalRankAnalytic.{uF, uU, uW} F (⟨⟩ : LocalFieldData F) r 0 0
    ψ ν hν μ VU V' π τ hπ hτ ℓU ℓ' hℓU hℓ'
  obtain ⟨a, ha⟩ := han.1 U W'
  refine ⟨a, fun s hs => ?_⟩
  have hc := (UnequalRankZeroRowAssembly.zero_row_converges_iff ψ abv 0 ν μ
    U.val W'.val s).mp (ha s hs)
  unfold CorankOneConverges
  exact hc.congr (Filter.Eventually.of_forall fun q =>
    unequalRankIntegrand_zero_zero ψ abv U.val W'.val s 0 q)

/-- Full Whittaker type discharges the quotient analytic inputs in the finite
product formula. Only actual shifted matrix values remain analytic premises. -/
theorem corankOneCoefficient_productContinuation {r N : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    [Measure.IsMulRightInvariant (unipotentHaar F r)]
    (ν : Measure (LeftUnipotentQuotient r F))
    (hν : IsCompatible (GeneralLinear.upperUnipotent (r + 1) F)
      (generalLinearHaar F r) (unipotentHaar F r) ν)
    (μ : AdditiveHaarMeasure F)
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V')
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1 + 1) F) VU)
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
    (f : Fin N → Langlands.GeneralLinear (r + 1) F → ℂ)
    (Lq Lh : ℤ)
    (hLq : ∀ g, W.val.val g ≠ 0 → φ (lastRow g) ≠ 0 →
      Lq ≤ (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant g : F))
    (hLh : ∀ h : Langlands.GeneralLinear (r + 1) F, Φ h.val ≠ 0 →
      Lh ≤ (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant h : F))
    (hc : ∀ m : ℤ, sliceCoefficient (⟨⟩ : LocalFieldData F) ν
      (corankOneIntegrand ψ abv U.val W'.val 0) m =
      ∑ k ∈ Finset.Icc Lq (m - Lh), ∑ i,
        equalRankSliceCoefficient (⟨⟩ : LocalFieldData F) ν ψ W.val (B i).val φ k *
          adjacentRankMatrixSliceCoefficient F Φ χ (f i) (m - k))
    (M : Fin N → RationalFunctions)
    (hM : ∀ i, GodementJacquet.HasShiftedRationalValue qF abv
      (generalLinearHaar F r) Φ
      (fun h => (χ (GeneralLinear.determinant h) : ℂ) * f i h) (M i)) :
    ∃ A : Fin N → RationalFunctions,
      (∀ i, HasRationalContinuation qF
        (fun s => equalRankIntegral ψ abv ν W.val (B i).val φ s) (A i)) ∧
      (∃ a : ℝ, ∀ s : ℂ, a < s.re →
        CorankOneConverges ψ abv ν U.val W'.val s ∧
        (∀ i, EqualRankConverges ψ abv ν W.val (B i).val φ s) ∧
        (∀ i, Langlands.AllField.GodementJacquet.Padic.MatrixConverges F Φ (s + (r : ℂ) / 2)
          (fun h => (χ (GeneralLinear.determinant h) : ℂ) * f i h)) ∧
        corankOneIntegral ψ abv ν U.val W'.val s =
          adjacentRankFiniteProductValue F ψ ν W.val (fun i => (B i).val)
            Φ φ χ f s) ∧
      HasRationalContinuation qF (fun s => corankOneIntegral ψ abv ν U.val W'.val s)
        (∑ i, A i * M i) ∧
      ∀ R, HasRationalContinuation qF
        (fun s => corankOneIntegral ψ abv ν U.val W'.val s) R →
        R = ∑ i, A i * M i := by
  classical
  have han := equalRankAnalytic.{uF, uV, uW} F (⟨⟩ : LocalFieldData F) r
    ψ ν hν V V' σ τ hσ hτ ℓ ℓ' hℓ hℓ'
  obtain ⟨aU, haU⟩ := corankOneCoefficient_convergesOnRight F ψ ν hν μ
    π τ hπ hτ ℓU ℓ' hℓU hℓ' U W'
  obtain ⟨aW, haW⟩ := UnequalRankReduction.finite_common_bound
    (fun i s => EqualRankConverges ψ abv ν W.val (B i).val φ s)
    (fun i => han.1 W (B i) φ)
  obtain ⟨aM, haM⟩ := UnequalRankReduction.finite_common_bound
    (fun i s => Langlands.AllField.GodementJacquet.Padic.MatrixConverges F Φ (s + (r : ℂ) / 2)
      (fun h => (χ (GeneralLinear.determinant h) : ℂ) * f i h))
    (fun i => (hM i).1)
  let a := max aU (max aW aM)
  have hright (s : ℂ) (hs : a < s.re) :
      CorankOneConverges ψ abv ν U.val W'.val s ∧
      (∀ i, EqualRankConverges ψ abv ν W.val (B i).val φ s) ∧
      (∀ i, Langlands.AllField.GodementJacquet.Padic.MatrixConverges F Φ (s + (r : ℂ) / 2)
        (fun h => (χ (GeneralLinear.determinant h) : ℂ) * f i h)) ∧
      corankOneIntegral ψ abv ν U.val W'.val s =
        adjacentRankFiniteProductValue F ψ ν W.val (fun i => (B i).val) Φ φ χ f s := by
    have hU := haU s ((le_max_left _ _).trans_lt hs)
    have hW := haW s ((le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hs)
    have hf := haM s ((le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hs)
    exact ⟨hU, hW, hf, corankOneIntegral_eq_finiteProducts_of_coefficients F ψ ν
      W.val (fun i => (B i).val) U.val W'.val Φ φ χ f Lq Lh hLq hLh hc s hU hW hf⟩
  choose A hA using fun i : Fin N => han.2.1 W (B i) φ
  have hcont : HasRationalContinuation qF
      (fun s => corankOneIntegral ψ abv ν U.val W'.val s) (∑ i, A i * M i) := by
    apply RationalContinuationLinear.continuation_of_eq_on_right
      (GodementJacquet.hasRationalContinuation_sum_mul Finset.univ
        (fun i s => equalRankIntegral ψ abv ν W.val (B i).val φ s)
        (fun i s => Langlands.AllField.GodementJacquet.Padic.matrixIntegral F Φ (s + (r : ℂ) / 2)
          (fun h => (χ (GeneralLinear.determinant h) : ℂ) * f i h))
        A M (fun i _ => hA i) (fun i _ => (hM i).2))
    exact ⟨a, fun s hs => (hright s hs).2.2.2⟩
  exact ⟨A, hA, ⟨a, hright⟩, hcont, fun R hR =>
    hR.unique (⟨⟩ : LocalFieldData F).residueCardinality_gt_one hcont⟩

end Langlands.AllField.RankinSelberg.Padic
