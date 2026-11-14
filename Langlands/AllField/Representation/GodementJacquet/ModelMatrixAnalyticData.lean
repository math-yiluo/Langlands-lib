import Langlands.Representation.GodementJacquet.ModelMatrixAnalyticData
import Langlands.AllField.Representation.GodementJacquet.ModelMatrixNormalizedGenerator
import Langlands.AllField.Representation.GodementJacquet.ModelWhittakerRationalityProof
import Langlands.AllField.Representation.GodementJacquet.UniformWhittakerMatrixConvergence
/-!
# Ordinary matrix analytic data on actual Whittaker models

Per-pair rationality, a common convergence bound and a normalized generator
are assembled on the actual coefficient image. The uniform Mellin input
is explicit.
-/

noncomputable section

namespace Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair ModelRationality NormalizedMatrixFunctionalEquationData averagingBorelSpace averagingLocalField averagingMeasurableSpace averagingSecondCountable averagingSigmaCompact averagingTopology averagingValuativeRel conjTest conjTest_apply exists_compactOpen_matrixTest_invariant exists_eq_sum_modelPointAverage exists_mem_jpssI3_of_coefficient exists_modelMatrixNormalizedGenerator exists_modelMatrixRationalValue exists_nhds_matrixTest_invariant exists_whittakerRationalValue glModelFunction_injective glModel_isAdmissible instAddCommGroupSubtypeForallGeneralLinearHAddNatOfNatCarrierComplexMemSubmoduleToSubmoduleEquivariantFunctionsUpperUnipotentStandardCharacterGlCoefficientModel instAddCommGroupSubtypeForallGeneralLinearHAddNatOfNatCarrierComplexMemSubmoduleToSubmoduleEquivariantFunctionsUpperUnipotentStandardCharacterGlCoefficientModel_1 instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instBorelSpaceGeneralLinearHAddNatOfNatCarrier_2 instBorelSpaceGeneralLinearHAddNatOfNatCarrier_3 instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instIsNonarchimedeanLocalFieldCarrier_3 instMeasurableSpaceCarrier instMeasurableSpaceCarrier_1 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_2 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_3 instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instTopologicalSpaceCarrier_3 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 instValuativeRelCarrier_3 integrable_conj_iff integral_conj iotaMatrixRationalValues isMatrixNormalizedGenerator_model_of_character isMatrixNormalizedGenerator_model_of_pair jpssI2 jpssI2_le_jpssI3_of_rationality jpssI3 jpssI3_le_jpssI2 matrixIntegral matrixIntegral_sum_modelPointAverage matrixIntegrand matrixIntegrand_conj matrixRationalValues matrixRationalValues_subset_jpssI3 measurableEmbedding_conj measurePreserving_conj measureReal_openSubgroup_ne_zero modelInclusionBorelSpace modelInclusionLocalField modelInclusionMeasurableSpace modelInclusionSecondCountable modelInclusionSigmaCompact modelInclusionTopology modelInclusionValuativeRel modelMatrixAnalyticAssertions modelMatrixLPolynomial modelMatrixLPolynomial_normalized modelMatrixLPolynomial_pair modelMatrixRationalValue modelMatrixRationalValue_spec modelPointAverage modelPointAverage_apply modelPointAverage_invariant modelPointAverage_matrixIntegral modelPointAverage_of_mem_fixedVectors modelSetIntegral modelSetIntegralDual whittakerRationalValues whittakerRationalValues_subset
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair ModelWhittakerRationalityStatement NormalizedMatrixFunctionalEquationData WhittakerModelComparisonStatement iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues modelWhittakerRationality whittakerModelComparison whittakerModelComparison_of_rationality whittakerRationalValues
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicRectangularHaarScaling padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement exists_compactOpen_glCoefficientRightStabilizer mirabolicUnitTest modelKirillovTransfer smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankFunctionalEquationStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement EqualRankUnitValueStatement FiniteFunctionMellinStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement RootTorusProductStatement SliceIntegrable SliceIntegrableAt SymmetricLPolynomialExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UniformFiniteFunctionMellinConvergenceStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankAnalytic equalRankCompactRootExpansion equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankNormalizedCompactIntegration equalRankQuotientAnalytic equalRankRootAverageAnalytic equalRankRootExpansion equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankUnitValue exists_rankOneCutoff exists_rankOneEmbedding_support finiteFunctionMellin finiteFunctionShellSeries hasEqualRankCompactTest_of_kirillov iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow oneVariableMellin pairwise_disjoint_determinantSlice quotientHaarExistence quotientIwasawaIntegration quotientRootIntegration rankOneCharacter_isOfWhittakerType rankOneMatrixWhittakerComparison rankOneMatrixWhittakerComparison_of_positive rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable symmetricLPolynomialExists unequalRankAnalytic unequalRankCommonGenerator unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIwasawaSupport unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unipotentHaar_mul_diagonal_le unipotentVolumeLocalField unipotentVolumeTopology unipotentVolumeValuativeRel whittakerRationalValues_eq_rankOneModelValues zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F) :=
  borel _
local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩

variable (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

local instance (ℓ : glFunctionals ψ n σ) :
    AddCommGroup (glCoefficientModel ψ n σ ℓ).toSubmodule :=
  (glCoefficientModel ψ n σ ℓ).toSubmodule.addCommGroup

/-- Every actual bi-smooth coefficient has a shifted rational value in the
Whittaker ideal of the original representation and specified functional. -/
theorem exists_modelMatrixRationalValue
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ)
    (ℓ : glFunctionals ψ n σ) (hℓ : ℓ.val ≠ 0)
    (Φ : MatrixTestFunction n F)
    (f : biSmoothMatrixCoefficients (glModelRepresentation ψ n σ ℓ)) :
    ∃ R : RationalFunctions,
      HasShiftedRationalValue (⟨⟩ : LocalFieldData F).residueCardinality
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (generalLinearHaar F n)
        Φ f.val R ∧ R ∈ jpssI3 F ψ σ ℓ := by
  apply exists_hasShiftedRationalValue_mem_of_generators (f := f)
  intro Λ w
  obtain ⟨R, hRmem, hR⟩ := exists_mem_jpssI3_of_coefficient F ψ σ hσ.1.1 ℓ
    (glModel_isAdmissible F ψ σ ℓ hσ.1)
    (modelWhittakerRationality F ψ n σ hσ ℓ hℓ)
    Λ w.val (biSmoothCoefficient _ Λ w) (biSmoothCoefficient_apply _ Λ w) Φ
  exact ⟨R, hR, hRmem⟩

/-- Choose an actual shifted rational continuation for each full-matrix test
and coefficient of the specified actual Whittaker model. -/
def modelMatrixRationalValue
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ)
    (ℓ : glFunctionals ψ n σ) (hℓ : ℓ.val ≠ 0)
    (Φ : MatrixTestFunction n F)
    (f : biSmoothMatrixCoefficients (glModelRepresentation ψ n σ ℓ)) : RationalFunctions :=
  (exists_modelMatrixRationalValue F ψ σ hσ ℓ hℓ Φ f).choose

/-- The chosen rational value is a continuation of the actual integral and
belongs to the original Whittaker ideal. -/
theorem modelMatrixRationalValue_spec
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ)
    (ℓ : glFunctionals ψ n σ) (hℓ : ℓ.val ≠ 0)
    (Φ : MatrixTestFunction n F)
    (f : biSmoothMatrixCoefficients (glModelRepresentation ψ n σ ℓ)) :
    HasShiftedRationalValue (⟨⟩ : LocalFieldData F).residueCardinality
        (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) (generalLinearHaar F n)
        Φ f.val (modelMatrixRationalValue F ψ σ hσ ℓ hℓ Φ f) ∧
      modelMatrixRationalValue F ψ σ hσ ℓ hℓ Φ f ∈ jpssI3 F ψ σ ℓ :=
  (exists_modelMatrixRationalValue F ψ σ hσ ℓ hℓ Φ f).choose_spec

/-- The chosen polynomial supplies the entire ordinary analytic predicate
on every nonzero actual coefficient model, under uniform Mellin convergence. -/
theorem modelMatrixAnalyticAssertions
    (hU : UniformFiniteFunctionMellinConvergenceStatement.{uF})
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ)
    (ℓ : glFunctionals ψ n σ) (hℓ : ℓ.val ≠ 0) :
    MatrixAnalyticAssertions F (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ) (modelMatrixLPolynomial F ψ σ ν hσ) := by
  refine ⟨Langlands.AllField.GodementJacquet.WhittakerTorus.Padic.glModel_matrixConvergesOnRight F hU ψ σ hσ ℓ, ?_,
    modelMatrixLPolynomial_normalized F ψ σ ν hσ ℓ hℓ⟩
  intro Φ f
  exact ⟨modelMatrixRationalValue F ψ σ hσ ℓ hℓ Φ f,
    (modelMatrixRationalValue_spec F ψ σ hσ ℓ hℓ Φ f).1⟩

end Langlands.AllField.GodementJacquet.Padic
