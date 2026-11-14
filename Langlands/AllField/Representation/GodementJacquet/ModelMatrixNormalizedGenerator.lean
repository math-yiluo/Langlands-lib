import Langlands.Representation.GodementJacquet.ModelMatrixNormalizedGenerator
import Langlands.AllField.Representation.GodementJacquet.WhittakerModelComparisonProof
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonProof
import Langlands.AllField.Representation.RankinSelberg.RankOneWhittakerTypeProof
import Langlands.AllField.Representation.RankinSelberg.SymmetricLPolynomialExistenceProof
/-!
# Normalized matrix generators on actual Whittaker coefficient models

Transport the published rank-one pair L-polynomial through `I₁ = I₃ = I₂`.
The carrier is the actual coefficient image, with no irreducibility premise.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankFunctionalEquationStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement EqualRankUnitValueStatement FiniteFunctionMellinStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement RootTorusProductStatement SliceIntegrable SliceIntegrableAt SymmetricLPolynomialExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankAnalytic equalRankCompactRootExpansion equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankNormalizedCompactIntegration equalRankQuotientAnalytic equalRankRootAverageAnalytic equalRankRootExpansion equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankUnitValue exists_rankOneCutoff exists_rankOneEmbedding_support finiteFunctionMellin finiteFunctionShellSeries hasEqualRankCompactTest_of_kirillov iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow oneVariableMellin pairwise_disjoint_determinantSlice quotientHaarExistence quotientIwasawaIntegration quotientRootIntegration rankOneCharacter_isOfWhittakerType rankOneMatrixWhittakerComparison rankOneMatrixWhittakerComparison_of_positive rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable symmetricLPolynomialExists unequalRankAnalytic unequalRankCommonGenerator unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIwasawaSupport unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unipotentHaar_mul_diagonal_le unipotentVolumeLocalField unipotentVolumeTopology unipotentVolumeValuativeRel whittakerRationalValues_eq_rankOneModelValues zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicRectangularHaarScaling padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement exists_compactOpen_glCoefficientRightStabilizer mirabolicUnitTest modelKirillovTransfer smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV

section CharacterGenerator


end CharacterGenerator

end Langlands.AllField.RankinSelberg

namespace Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair ModelRationality NormalizedMatrixFunctionalEquationData averagingBorelSpace averagingLocalField averagingMeasurableSpace averagingSecondCountable averagingSigmaCompact averagingTopology averagingValuativeRel conjTest conjTest_apply exists_compactOpen_matrixTest_invariant exists_eq_sum_modelPointAverage exists_mem_jpssI3_of_coefficient exists_modelMatrixNormalizedGenerator exists_nhds_matrixTest_invariant exists_whittakerRationalValue glModelFunction_injective glModel_isAdmissible instAddCommGroupSubtypeForallGeneralLinearHAddNatOfNatCarrierComplexMemSubmoduleToSubmoduleEquivariantFunctionsUpperUnipotentStandardCharacterGlCoefficientModel instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instBorelSpaceGeneralLinearHAddNatOfNatCarrier_2 instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instMeasurableSpaceCarrier instMeasurableSpaceCarrier_1 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_2 instMeasurableSpaceLeftUnipotentQuotientCarrier instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 integrable_conj_iff integral_conj iotaMatrixRationalValues isMatrixNormalizedGenerator_model_of_character isMatrixNormalizedGenerator_model_of_pair jpssI2 jpssI2_le_jpssI3_of_rationality jpssI3 jpssI3_le_jpssI2 matrixIntegral matrixIntegral_sum_modelPointAverage matrixIntegrand matrixIntegrand_conj matrixRationalValues matrixRationalValues_subset_jpssI3 measurableEmbedding_conj measurePreserving_conj measureReal_openSubgroup_ne_zero modelInclusionBorelSpace modelInclusionLocalField modelInclusionMeasurableSpace modelInclusionSecondCountable modelInclusionSigmaCompact modelInclusionTopology modelInclusionValuativeRel modelMatrixLPolynomial modelMatrixLPolynomial_normalized modelMatrixLPolynomial_pair modelPointAverage modelPointAverage_apply modelPointAverage_invariant modelPointAverage_matrixIntegral modelPointAverage_of_mem_fixedVectors modelSetIntegral modelSetIntegralDual whittakerRationalValues whittakerRationalValues_subset
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair ModelWhittakerRationalityStatement NormalizedMatrixFunctionalEquationData WhittakerModelComparisonStatement iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues whittakerModelComparison whittakerModelComparison_of_rationality whittakerRationalValues
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicRectangularHaarScaling padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement exists_compactOpen_glCoefficientRightStabilizer mirabolicUnitTest modelKirillovTransfer smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankFunctionalEquationStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement EqualRankUnitValueStatement FiniteFunctionMellinStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement RootTorusProductStatement SliceIntegrable SliceIntegrableAt SymmetricLPolynomialExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankAnalytic equalRankCompactRootExpansion equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankNormalizedCompactIntegration equalRankQuotientAnalytic equalRankRootAverageAnalytic equalRankRootExpansion equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankUnitValue exists_rankOneCutoff exists_rankOneEmbedding_support finiteFunctionMellin finiteFunctionShellSeries hasEqualRankCompactTest_of_kirillov iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow oneVariableMellin pairwise_disjoint_determinantSlice quotientHaarExistence quotientIwasawaIntegration quotientRootIntegration rankOneCharacter_isOfWhittakerType rankOneMatrixWhittakerComparison rankOneMatrixWhittakerComparison_of_positive rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable symmetricLPolynomialExists unequalRankAnalytic unequalRankCommonGenerator unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIwasawaSupport unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unipotentHaar_mul_diagonal_le unipotentVolumeLocalField unipotentVolumeTopology unipotentVolumeValuativeRel whittakerRationalValues_eq_rankOneModelValues zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance : MeasurableSpace F := borel _
local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n F) := borel _

variable (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

local instance (ℓ : glFunctionals ψ n σ) :
    AddCommGroup (glCoefficientModel ψ n σ ℓ).toSubmodule :=
  (glCoefficientModel ψ n σ ℓ).toSubmodule.addCommGroup

/-- A character L-generator is the ordinary matrix generator on every
nonzero coefficient model, by the two published ideal comparisons. -/
theorem isMatrixNormalizedGenerator_model_of_character
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ)
    (ℓ : glFunctionals ψ n σ) (hℓ : ℓ.val ≠ 0)
    [Measure.IsMulRightInvariant (unipotentHaar F 0)]
    (μ : Measure (LeftUnipotentQuotient 0 F))
    (hμ : IsCompatible (upperUnipotent (0 + 1) F)
      (generalLinearHaar F 0) (unipotentHaar F 0) μ)
    {P : Polynomial ℂ}
    (hP : IsCharacterLPolynomial (⟨⟩ : LocalFieldData F).residueCardinality ψ
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) μ 1 σ P) :
    IsMatrixNormalizedGenerator F (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ) P := by
  have h13 := rankOneMatrixWhittakerComparison F ψ n V σ hσ ℓ hℓ μ hμ
  have h23 := Langlands.AllField.GodementJacquet.whittakerModelComparison F ψ n σ hσ ℓ hℓ
  exact (isNormalizedGenerator_congr (h13.trans h23.symm) P).1 hP

/-- One full symmetric pair certificate supplies the ordinary normalized
matrix generator on every nonzero actual coefficient model. -/
theorem isMatrixNormalizedGenerator_model_of_pair
    (ν : AdditiveHaarMeasure F)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ)
    {P : Polynomial ℂ}
    (hP : IsPadicSymmetricLPolynomial F ψ ν σ (rankOneCharacter 1) P)
    (ℓ : glFunctionals ψ n σ) (hℓ : ℓ.val ≠ 0) :
    IsMatrixNormalizedGenerator F (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ) P := by
  have hp := (isPadicSymmetricLPolynomial_of_le (Nat.zero_le n)).1 hP
  obtain ⟨⟨hinv, μ, hμ⟩, hgen⟩ := hp
  let := hinv
  exact isMatrixNormalizedGenerator_model_of_character F ψ σ hσ ℓ hℓ μ hμ
    ((hgen μ hμ).isCharacterLPolynomial)

/-- Existence retains the complete symmetric L-certificate and gives a
single polynomial for all nonzero functionals on the original carrier. -/
theorem exists_modelMatrixNormalizedGenerator
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ) :
    ∃ P : Polynomial ℂ,
      IsPadicSymmetricLPolynomial F ψ ν.val σ (rankOneCharacter 1) P ∧
      ∀ ℓ : glFunctionals ψ n σ, ℓ.val ≠ 0 →
        IsMatrixNormalizedGenerator F (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
          (glModelRepresentation ψ n σ ℓ) P := by
  have h1 := rankOneCharacter_isOfWhittakerType F ψ (1 : Quasicharacter F)
  obtain ⟨P, hP⟩ := symmetricLPolynomialExists F ψ ν n 0 V ℂ σ
    (rankOneCharacter 1) hσ h1
  exact ⟨P, hP, fun ℓ hℓ => isMatrixNormalizedGenerator_model_of_pair F ψ σ ν.val hσ hP ℓ hℓ⟩

/-- The ordinary matrix polynomial chosen from the full pair L-existence
theorem. Its generator property concerns the actual coefficient models. -/
def modelMatrixLPolynomial
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ) : Polynomial ℂ :=
  (exists_modelMatrixNormalizedGenerator F ψ σ ν hσ).choose

/-- The chosen polynomial retains the full supplied-measure pair certificate. -/
theorem modelMatrixLPolynomial_pair
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ) :
    IsPadicSymmetricLPolynomial F ψ ν.val σ (rankOneCharacter 1)
      (modelMatrixLPolynomial F ψ σ ν hσ) :=
  (exists_modelMatrixNormalizedGenerator F ψ σ ν hσ).choose_spec.1

/-- The chosen polynomial generates the ordinary matrix values on each
actual nonzero coefficient model of the original representation. -/
theorem modelMatrixLPolynomial_normalized
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    (hσ : IsOfWhittakerType n (standardCharacter ψ n) σ)
    (ℓ : glFunctionals ψ n σ) (hℓ : ℓ.val ≠ 0) :
    IsMatrixNormalizedGenerator F (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ)
      (modelMatrixLPolynomial F ψ σ ν hσ) :=
  (exists_modelMatrixNormalizedGenerator F ψ σ ν hσ).choose_spec.2 ℓ hℓ

end Langlands.AllField.GodementJacquet.Padic
