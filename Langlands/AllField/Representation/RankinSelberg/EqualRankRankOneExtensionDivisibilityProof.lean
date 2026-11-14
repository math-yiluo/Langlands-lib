import Langlands.Representation.RankinSelberg.EqualRankRankOneExtensionDivisibilityProof
import Langlands.AllField.Representation.RankinSelberg.EqualRankRankOneExtensionDivisibilityStatement
import Langlands.AllField.Representation.RankinSelberg.EqualRankRankOneExtensionSpanComparisonProof
import Langlands.AllField.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof
import Langlands.AllField.Representation.RankinSelberg.SymmetricLPolynomialExistenceProof
/-!
# Equal-rank rank-one extension reverse L-divisibility: proof
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankFunctionalEquationStatement EqualRankLastRowReductionStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRankOneExtensionLDivisibilityStatement EqualRankRankOneExtensionSpanComparisonStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement EqualRankUnitValueStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RankOneExtensionLDivisibilityStatement RankOneExtensionSpanComparisonStatement RankOneWhittakerTypeStatement RootTorusProductStatement SliceIntegrable SliceIntegrableAt SymmetricLPolynomialExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankAnalytic equalRankCompactRootExpansion equalRankExtensionFamily equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankLastRowReduction equalRankNormalizedCompactIntegration equalRankQuotientAnalytic equalRankRankOneExtensionLDivisibility equalRankRankOneExtensionSpanComparison equalRankRankOneExtensionSpanComparison_of equalRankRankOneExtensionSpanComparison_of_rowFourierSurjectivity equalRankRootAverageAnalytic equalRankRootExpansion equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSpanComparison_core equalRankUnitValue exists_inverseWhittaker_twoBlockExtension finiteFunctionMellin finiteFunctionShellSeries half_mul_determinantWeight hasEqualRankCompactTest_of_kirillov iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOfWhittakerType_equalRankExtension isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt iwasawaTorusSum lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow normalizedProductWhittakerType oneVariableMellin pairwise_disjoint_determinantSlice quotientHaarExistence quotientIwasawaIntegration quotientRootIntegration rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneExtensionLowerFamily rankOneExtensionLowerInduced rankOneExtensionLowerModel rankOneExtensionLowerSection rankOneExtensionLowerSectionCoefficient rankOneExtensionLowerSectionEval rankOneExtensionLowerToUpperEquiv rankOneExtensionSpanComparison_of_pointwise rankOneExtensionWhittakerContraction rankOneWhittakerType rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable symmetricLPolynomialExists unequalRankAnalytic unequalRankCommonGenerator unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIwasawaSupport unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Polynomial
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicMatrixFourierSlice padicRectangularHaarScaling padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding CompactLocalizationStatement MirabolicUnitTestStatement TwoBlockCellCoefficientStatement TwoBlockCellJacquetIntegrabilityStatement TwoBlockCellSectionStatement TwoBlockCellUnipotentStabilityStatement TwoBlockExtensionAssemblyStatement TwoBlockInducedCarrier TwoBlockInducingWhittakerCovarianceStatement TwoBlockJacquetCovarianceStatement TwoBlockJacquetFunctionalExtensionStatement TwoBlockLeadingTranslationStatement TwoBlockWhittakerExtensionStatement UnipotentOrbitStatement compactLocalization exchangedParabolic exists_compactOpen_glCoefficientRightStabilizer exists_openSubgroup_subset_parabolic_mul_opposite functionalsCongr hasCompactSupport_twoBlockCellRestriction inducedLocalization_of_prerequisites mirabolicUnitTest modelKirillovTransfer mul_upperUnipotent_mem_twoBlockCell oppositeLower smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellCoefficient twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellJacquetIntegrability twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSection twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockHalfModulus_mul_detPow twoBlockInduced twoBlockInducingRepresentation twoBlockInducingWhittakerCovariance twoBlockJacquetCovariance twoBlockJacquetFunctionalExtension twoBlockLeadingTranslation twoBlockParabolic twoBlockRestriction twoBlockWhittakerExtension_of_rowFourierSurjectivity unipotentLeviFactor unipotentOrbit unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

section Shape


/-- The blocks `(χ, σ₁)` indexed by the ranks `equalRankExtensionRanks t`. -/
def equalRankExtensionFamily {F : Type uF} [Field F] {t : ℕ} {C W : Type uW}
    [AddCommGroup C] [Module ℂ C] [AddCommGroup W] [Module ℂ W]
    (χrep : Representation ℂ (Langlands.GeneralLinear 1 F) C)
    (σ₁ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W)
    (i : Fin 2) : Representation ℂ
      (Langlands.GeneralLinear (equalRankExtensionRanks t i + 1) F)
      (Shahidi.pairCarrier C W i) :=
  match i with
  | 0 => χrep
  | 1 => σ₁

/-- The full Whittaker type of the upper normalized induction of `(χ, σ₁)`, from
the published theorem `normalizedProductWhittakerType` for successor block
shapes. -/
theorem isOfWhittakerType_equalRankExtension
    (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    {t : ℕ} {C W : Type uW} [AddCommGroup C] [Module ℂ C] [AddCommGroup W] [Module ℂ W]
    (χrep : Representation ℂ (Langlands.GeneralLinear 1 F) C)
    (σ₁ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W)
    (hχ : IsOfWhittakerType 0 (standardCharacter ψ 0) χrep)
    (hσ : IsOfWhittakerType t (standardCharacter ψ t) σ₁) :
    IsOfWhittakerType (1 + t) (standardCharacter ψ (1 + t))
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced
        (Shahidi.twoBlocks 1 (t + 1) (Nat.succ_pos 0) (Nat.succ_pos t))
        (Shahidi.pairFamily χrep σ₁)) := by
  let D := Σ s : {s : Fin 2 → ℕ // (∀ i, 0 < s i) ∧ ∑ i, s i = (1 + t) + 1},
    ∀ i, Representation ℂ (Langlands.GeneralLinear (s.val i) F)
      (Shahidi.pairCarrier C W i)
  let d₀ : D := ⟨⟨fun i => equalRankExtensionRanks t i + 1,
    ⟨fun i => Nat.succ_pos _, equalRankExtensionRankSum t⟩⟩,
    equalRankExtensionFamily χrep σ₁⟩
  let d₁ : D := ⟨⟨![1, t + 1], ⟨by intro i; fin_cases i <;> exact Nat.succ_pos _,
    by simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]; omega⟩⟩,
    Shahidi.pairFamily χrep σ₁⟩
  have hd : d₀ = d₁ := by
    apply Sigma.ext
    · apply Subtype.ext
      funext i
      fin_cases i <;> rfl
    · apply Function.hfunext rfl
      intro i j hij
      have hij' : i = j := eq_of_heq hij
      subst j
      fin_cases i <;> rfl
  let wt : D → Prop := fun d =>
    IsOfWhittakerType (1 + t) (standardCharacter ψ (1 + t))
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced ⟨2, d.1.val, d.1.property.1, d.1.property.2⟩ d.2)
  change wt d₁
  rw [← hd]
  apply normalizedProductWhittakerType.{uF, uW} F ψ (1 + t) 2 (equalRankExtensionRanks t) (equalRankExtensionRankSum t)
    (equalRankExtensionFamily χrep σ₁)
  intro i
  fin_cases i
  · exact hχ
  · exact hσ

end Shape

/-- Reverse L-divisibility for the equal-rank rank-one extension, from the
published `symmetricLPolynomialExists`, `normalizedProductWhittakerType` and
`equalRankRankOneExtensionSpanComparison`. -/
theorem equalRankRankOneExtensionLDivisibility :
    EqualRankRankOneExtensionLDivisibilityStatement.{uF, uV, uW} := by
  intro F _ _ _ _ ψ ν t V _ _ W _ _ π σ₁ χ hπ hσ χlift
  have hχ : IsOfWhittakerType 0 (standardCharacter ψ 0) χlift :=
    (rankOneCharacter_isOfWhittakerType F ψ χ).of_equiv (conjULiftEquiv _)
  have hI := isOfWhittakerType_equalRankExtension F ψ χlift σ₁ hχ hσ
  obtain ⟨Pbase, hb⟩ := symmetricLPolynomialExists.{uF, uV, uW}
    F ψ ν (t + 1) t V W π σ₁ hπ hσ
  obtain ⟨Pind, hi⟩ := symmetricLPolynomialExists.{uF, uV, max uF uW}
    F ψ ν (t + 1) (1 + t) V _ π _ hπ hI
  refine ⟨Pbase, Pind, hb, hi, ?_⟩
  let := borel F
  have : BorelSpace F := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient t F)
  let := borel (LeftUnipotentQuotient (1 + t) F)
  rw [isPadicSymmetricLPolynomial_of_le (by omega)] at hb
  rw [isPadicSymmetricLPolynomial_of_le (show 1 + t ≤ t + 1 by omega)] at hi
  obtain ⟨⟨_, μb, hμb⟩, hb'⟩ := hb
  obtain ⟨⟨_, μi, hμi⟩, hi'⟩ := hi
  have hrn : t + 1 = 1 + t := by omega
  have gb := (isPairLPolynomial_of_lt (by omega)).1 (hb' μb hμb) 0 0 rfl
  have gi := hi' μi hμi
  rw [IsPairLPolynomial, ite_eq_right (show ¬ (1 + t < t + 1) by omega), dite_eq_left hrn] at gi
  exact (laurentPolynomialDivisibility.2.2 _ _ _ _ gb gi).1
    (equalRankRankOneExtensionSpanComparison.{uF, uV, uW}
      F ψ ν.val t π σ₁ χ hπ hσ μb μi hμb hμi hrn)

end Langlands.AllField.RankinSelberg
