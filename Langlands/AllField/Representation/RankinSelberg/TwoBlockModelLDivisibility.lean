import Langlands.Representation.RankinSelberg.TwoBlockModelLDivisibility
import Langlands.AllField.Representation.GodementJacquet.ModelMatrixAnalyticData
import Langlands.AllField.Representation.GodementJacquet.TwoBlockReverseRealization
import Langlands.AllField.Representation.RankinSelberg.InducedWhittakerQuotient
import Langlands.AllField.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonModels
import Langlands.AllField.Representation.RankinSelberg.RankOneTestReduction
/-!
# L-divisibility through induction of the actual coefficient quotients

The uniform Mellin premise remains explicit. No functional equation is needed.
-/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding ModelWhittakerRationalityStatement WhittakerModelComparisonStatement compactInducedCoefficientKernel compactProductPairingKernel exists_compactInducedCoefficientFormula exists_compactProductCoefficientFormula exists_compactProductPairing_expansion modelWhittakerRationality padicMatrixFourierPair_compact_left_invariant padicMatrixFourierPair_leftRight_invariant whittakerModelComparison whittakerModelComparison_of_rationality
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding CompactLocalizationStatement MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier UnipotentOrbitStatement compactLocalization exchangedParabolic exists_compactOpen_glCoefficientRightStabilizer hasCompactSupport_twoBlockCellRestriction inducedLocalization_of_prerequisites mirabolicUnitTest modelKirillovTransfer mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentOrbit unipotentShift
open Langlands.AllField.Whittaker
open Langlands.RankinSelberg hiding CharacterChangeCompatibleMeasureStatement EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankFactorSwapStatement EqualRankFunctionalEquationStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement EqualRankUnitValueStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RankOneCharacterReductionStatement RankOneGammaTwistStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement RootTorusProductStatement SliceIntegrable SliceIntegrableAt SymmetricLPolynomialExistenceStatement TwoBlockGammaAdjacentRankStatement TwoBlockGammaDominantRankStatement TwoBlockGammaRankOneStatement TwoBlockLAdjacentRankStatement TwoBlockLDominantRankStatement TwoBlockLRankOneStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UniformFiniteFunctionMellinConvergenceStatement UnipotentCharacterChangeModulusStatement ZeroRowLastRowCutoffStatement characterChangeCompatibleMeasure characterChangeCompatibleMeasure_of_unipotentModulus continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankAnalytic equalRankCompactRootExpansion equalRankFactorSwap equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankNormalizedCompactIntegration equalRankQuotientAnalytic equalRankRootAverageAnalytic equalRankRootExpansion equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankUnitValue exists_rankOneCutoff exists_rankOneEmbedding_support finiteFunctionMellin finiteFunctionShellSeries glCoefficientModel_isOfWhittakerType hasEqualRankCompactTest_of_kirillov iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOfWhittakerType_quasicharacter_twist_iff isOpen_determinantSlice isPadicPairEpsilonFactor_swap_equalRank isPadicPairGammaFactor_swap_equalRank isPadicPairLPolynomial_swap_equalRank isPadicPairLPolynomial_twist isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricGammaFactor_rankOne_test_twist isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt isPadicSymmetricLPolynomial_rankOne_one_swap isPadicSymmetricLPolynomial_rankOne_test_twist isPadicSymmetricLPolynomial_twist iwasawaTorusSum lastRowCompactOrbit leviModulus_characterChangeLevi leviModulus_characterChangeLevi_eq_pow matrixComparisonModelsTopology measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer model_jpssI2_le_of_surjective normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow normalizedProductWhittakerType oneVariableMellin pairwise_disjoint_determinantSlice quasicharacterSmoothCharacter quasicharacter_isOpen_ker quotientHaarExistence quotientIwasawaIntegration quotientRootIntegration rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneGammaTwist rankOneMatrixWhittakerComparison rankOneMatrixWhittakerComparison_of_positive rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable symmetricLPolynomialExists twoBlockGammaRankOne_of_trivial_test twoBlockLRankOne_of_trivial_test twoBlockLRankOne_of_uniform_mellin twoBlockModelLTopology unequalRankAnalytic unequalRankCommonGenerator unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIwasawaSupport unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unipotentCharacterChangeModulus unipotentHaar_mul_diagonal_le unipotentVolumeLocalField unipotentVolumeTopology unipotentVolumeValuativeRel whittakerRationalValues_eq_rankOneModelValues zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

universe uG uF uV uW

end Langlands.AllField.GodementJacquet

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding CharacterChangeCompatibleMeasureStatement EqualRankAnalyticStatement EqualRankCompactRootExpansionStatement EqualRankFactorSwapStatement EqualRankFunctionalEquationStatement EqualRankNormalizedCompactIntegrationStatement EqualRankQuotientAnalyticStatement EqualRankRootAverageAnalyticStatement EqualRankRootExpansionStatement EqualRankUnitValueStatement FiniteFunctionMellinStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement QuotientIwasawaIntegrationStatement RankOneCharacterReductionStatement RankOneGammaTwistStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement RootTorusProductStatement SliceIntegrable SliceIntegrableAt SymmetricLPolynomialExistenceStatement TwoBlockGammaAdjacentRankStatement TwoBlockGammaDominantRankStatement TwoBlockGammaRankOneStatement TwoBlockLAdjacentRankStatement TwoBlockLDominantRankStatement TwoBlockLRankOneStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UniformFiniteFunctionMellinConvergenceStatement UnipotentCharacterChangeModulusStatement ZeroRowLastRowCutoffStatement characterChangeCompatibleMeasure characterChangeCompatibleMeasure_of_unipotentModulus continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map diagonal_abs_bound diagonal_abs_last disjoint_determinantSlice equalRankAnalytic equalRankCompactRootExpansion equalRankFactorSwap equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankNormalizedCompactIntegration equalRankQuotientAnalytic equalRankRootAverageAnalytic equalRankRootExpansion equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankUnitValue exists_rankOneCutoff exists_rankOneEmbedding_support finiteFunctionMellin finiteFunctionShellSeries glCoefficientModel_isOfWhittakerType hasEqualRankCompactTest_of_kirillov iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOfWhittakerType_quasicharacter_twist_iff isOpen_determinantSlice isPadicPairEpsilonFactor_swap_equalRank isPadicPairGammaFactor_swap_equalRank isPadicPairLPolynomial_swap_equalRank isPadicPairLPolynomial_twist isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricGammaFactor_rankOne_test_twist isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt isPadicSymmetricLPolynomial_rankOne_one_swap isPadicSymmetricLPolynomial_rankOne_test_twist isPadicSymmetricLPolynomial_twist iwasawaTorusSum lastRowCompactOrbit leviModulus_characterChangeLevi leviModulus_characterChangeLevi_eq_pow matrixComparisonModelsTopology measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelAsymptoticTransfer model_jpssI2_le_of_surjective normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow normalizedProductWhittakerType oneVariableMellin pairwise_disjoint_determinantSlice quasicharacterSmoothCharacter quasicharacter_isOpen_ker quotientHaarExistence quotientIwasawaIntegration quotientRootIntegration rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneGammaTwist rankOneMatrixWhittakerComparison rankOneMatrixWhittakerComparison_of_positive rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rightTranslate_mem_determinantSlice rootCoordinateChange rootCoordinateFiniteFunction rootSpectralWeight rootTorusProduct setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable symmetricLPolynomialExists twoBlockGammaRankOne_of_trivial_test twoBlockLRankOne_of_trivial_test twoBlockLRankOne_of_uniform_mellin twoBlockModelLTopology unequalRankAnalytic unequalRankCommonGenerator unequalRankCompactSupport unequalRankFiniteExpansion unequalRankIwasawaSupport unequalRankUnitSpan unequalRankZeroRowNormalizedCompactIntegration unequalRankZeroRowRootExpansion unipotentCharacterChangeModulus unipotentHaar_mul_diagonal_le unipotentVolumeLocalField unipotentVolumeTopology unipotentVolumeValuativeRel whittakerRationalValues_eq_rankOneModelValues zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Polynomial
open Langlands.HarmonicAnalysis hiding PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding CompactLocalizationStatement MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier UnipotentOrbitStatement compactLocalization exchangedParabolic exists_compactOpen_glCoefficientRightStabilizer functionalsCongr hasCompactSupport_twoBlockCellRestriction inducedLocalization_of_prerequisites mirabolicUnitTest modelKirillovTransfer mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentOrbit unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear

universe uF uV uW

section ModelInclusion

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance twoBlockModelLGLMeasurable {n : ℕ} : MeasurableSpace (Langlands.GeneralLinear (n + 1) F) :=
  borel _

/-- The coefficient model of a full-type source is a genuine quotient of
any smooth quotient with a nonzero functional. Only the models are identified. -/
theorem model_jpssI2_le_of_surjective
    (ψ : UnitaryAdditiveCharacter F) {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (hρ : IsOfWhittakerType n (standardCharacter ψ n) ρ)
    (hτ : IsSmooth τ) (q : ρ.IntertwiningMap τ) (hq : Function.Surjective q)
    (ℓ : glFunctionals ψ n ρ) (hℓ : ℓ.val ≠ 0)
    (ℓ' : glFunctionals ψ n τ) (hℓ' : ℓ'.val ≠ 0) :
    Langlands.AllField.GodementJacquet.Padic.jpssI2 F
        (V := (glCoefficientModel ψ n ρ ℓ).toSubmodule)
        (glModelRepresentation ψ n ρ ℓ) ≤
      Langlands.AllField.GodementJacquet.Padic.jpssI2 F τ := by
  let : AddCommGroup (glCoefficientModel ψ n ρ ℓ).toSubmodule :=
    (glCoefficientModel ψ n ρ ℓ).toSubmodule.addCommGroup
  let : AddCommGroup (glCoefficientModel ψ n τ ℓ').toSubmodule :=
    (glCoefficientModel ψ n τ ℓ').toSubmodule.addCommGroup
  have heq := coefficientModel_eq_of_surjective_of_whittakerType hρ q hq ℓ ℓ' hℓ hℓ'
  let e : (glModelRepresentation ψ n ρ ℓ).Equiv
      (glModelRepresentation ψ n τ ℓ') :=
    Representation.Equiv.mk
      (LinearEquiv.ofEq (glCoefficientModel ψ n ρ ℓ).toSubmodule
        (glCoefficientModel ψ n τ ℓ').toSubmodule
        (congrArg Subrepresentation.toSubmodule heq))
      (fun _ => by ext w; rfl)
  have hcoeff : GodementJacquet.biSmoothMatrixCoefficients
      (glModelRepresentation ψ n ρ ℓ) ≤ GodementJacquet.biSmoothMatrixCoefficients τ := by
    rw [GodementJacquet.biSmoothMatrixCoefficients_equiv e]
    exact GodementJacquet.biSmoothMatrixCoefficients_le_of_surjective hτ
      (modelMap τ ℓ') (modelMap_surjective τ ℓ')
  exact Submodule.span_mono
    (GodementJacquet.matrixRationalValues_subset_of_coefficients_le _ _ _ hcoeff)

end ModelInclusion

/-- Exchange the trivial scalar test with the other member, retaining the
entire symmetric certificate even in rank one. -/
theorem isPadicSymmetricLPolynomial_rankOne_one_swap
    (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : letI := borel F
      AdditiveHaarMeasure F)
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (P : Polynomial ℂ) :
    IsPadicSymmetricLPolynomial F ψ ν σ (rankOneCharacter 1) P ↔
      IsPadicSymmetricLPolynomial F ψ ν (rankOneCharacter 1) σ P := by
  cases n with
  | zero =>
    simp only [IsPadicSymmetricLPolynomial, Nat.le_refl, ite_true]
    exact isPadicPairLPolynomial_swap_equalRank F ψ ν σ (rankOneCharacter 1) P
  | succ n =>
    simp only [IsPadicSymmetricLPolynomial, Nat.zero_le,
      show ¬ n + 1 ≤ 0 by omega, ite_true, ite_false]

set_option maxHeartbeats 800000 in
/-- The full rank-one L base follows from the ordinary model analytics,
with the uniform Mellin convergence assertion still supplied explicitly. -/
theorem twoBlockLRankOne_of_uniform_mellin
    (hU : UniformFiniteFunctionMellinConvergenceStatement.{uF}) :
    TwoBlockLRankOneStatement.{uF,uV,uW} := by
  apply twoBlockLRankOne_of_trivial_test
  intro F _ _ _ _ ψ ν t m h W hadd hmod σ hσ
  let : ∀ n : ℕ, MeasurableSpace (Langlands.GeneralLinear (n + 1) F) :=
    fun _ => borel _
  let : ∀ n : ℕ, BorelSpace (Langlands.GeneralLinear (n + 1) F) :=
    fun _ => ⟨rfl⟩
  choose ℓ hℓ using fun i => (hσ i).exists_ne_zero
  let M : Fin 2 → Type uF :=
    fun i => (glCoefficientModel ψ (m i) (σ i) (ℓ i)).toSubmodule
  let : ∀ i, AddCommGroup (M i) :=
    fun i => (glCoefficientModel ψ (m i) (σ i) (ℓ i)).toSubmodule.addCommGroup
  let : ∀ i, Module ℂ (M i) := fun i => inferInstance
  let τ (i : Fin 2) : Representation ℂ
      (Langlands.GeneralLinear (m i + 1) F) (M i) :=
    glModelRepresentation ψ (m i) (σ i) (ℓ i)
  have hτ (i : Fin 2) : IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i) :=
    glCoefficientModel_isOfWhittakerType F ψ (σ i) (hσ i) (ℓ i) (hℓ i)
  let Pi : Fin 2 → Polynomial ℂ :=
    fun i => Langlands.AllField.GodementJacquet.Padic.modelMatrixLPolynomial F ψ (σ i) ν (hσ i)
  have hblock (i : Fin 2) : Langlands.AllField.GodementJacquet.Padic.MatrixAnalyticAssertions F (τ i) (Pi i) :=
    Langlands.AllField.GodementJacquet.Padic.modelMatrixAnalyticAssertions F ψ (σ i) hU ν (hσ i) (ℓ i) (hℓ i)
  let I := (⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) σ
  let J := (⟨⟩ : LocalFieldData F).normalizedProductInduced (succBlockShape m h) τ
  have hI : IsOfWhittakerType t (standardCharacter ψ t) I :=
    normalizedProductWhittakerType F ψ t 2 m h σ hσ
  have hJ : IsOfWhittakerType t (standardCharacter ψ t) J :=
    normalizedProductWhittakerType F ψ t 2 m h τ hτ
  have hJan : Langlands.AllField.GodementJacquet.Padic.MatrixAnalyticAssertions F J (∏ i, Pi i) :=
    GodementJacquet.matrixAnalyticAssertions_twoBlock_of_generators _
      (⟨⟩ : LocalFieldData F).residueCardinality_gt_one _ _ _ m _ τ Pi hblock
      (Langlands.AllField.GodementJacquet.TwoBlock.twoBlock_matrixGeneratorInputs F h τ
        (fun i => (hτ i).1.1) (fun i => (hτ i).1) Pi hblock)
  let q : I.IntertwiningMap J :=
    (⟨⟩ : LocalFieldData F).normalizedProductModelMap (succBlockShape m h) σ ℓ
  have hq : Function.Surjective q :=
    (⟨⟩ : LocalFieldData F).normalizedProductModelMap_surjective
      (succBlockShape m h) σ (fun i => (hσ i).1.1) ℓ
  obtain ⟨ℓI, hℓI⟩ := hI.exists_ne_zero
  obtain ⟨ℓJ, hℓJ⟩ := hJ.exists_ne_zero
  let P := Langlands.AllField.GodementJacquet.Padic.modelMatrixLPolynomial F ψ I ν hI
  have hP := Langlands.AllField.GodementJacquet.Padic.modelMatrixLPolynomial_pair F ψ I ν hI
  have hPgen := Langlands.AllField.GodementJacquet.Padic.modelMatrixLPolynomial_normalized F ψ I ν hI ℓI hℓI
  have hle := model_jpssI2_le_of_surjective F ψ I J hI hJ.1.1 q hq ℓI hℓI ℓJ hℓJ
  have hdiv : P ∣ ∏ i, Pi i :=
    (normalizedGeneratorSpanDivisibility _ _ P (∏ i, Pi i) hPgen hJan.2.2).1 hle
  refine ⟨P, Pi, (isPadicSymmetricLPolynomial_rankOne_one_swap F ψ ν.val I P).1 hP,
    fun i => ?_, ?_⟩
  · exact (isPadicSymmetricLPolynomial_rankOne_one_swap F ψ ν.val (σ i) (Pi i)).1
      (Langlands.AllField.GodementJacquet.Padic.modelMatrixLPolynomial_pair F ψ (σ i) ν (hσ i))
  · obtain ⟨Q, hQ⟩ := hdiv
    exact ⟨Q, 0, by rw [pow_zero, one_mul]; exact hQ.trans (mul_comm _ _)⟩

end Langlands.AllField.RankinSelberg
