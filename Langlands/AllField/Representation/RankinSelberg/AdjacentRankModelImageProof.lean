import Langlands.Representation.RankinSelberg.AdjacentRankModelImageProof
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankAdmissibility
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankInvariantApproximation
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankJacquetLimit
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankJacquetNonzero
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankModelImageStatement
/-! Whole-function image equality for the actual normalized adjacent induction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllField.RankinSelberg.AdjacentJacquet
open Langlands.RankinSelberg.AdjacentJacquet hiding compactTestModelTensor compactTestModelTensor_tmul determinantWeight_eq exists_constantKernel_section functional functional_coefficient functional_ne_zero inducedRepresentation inducing_isSmooth instBorelSpaceCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instTotallyDisconnectedSpaceCarrier instValuativeRelCarrier integrable_normalizedSection_realTwist integrable_realTwist integral integralLinear integralLinear_apply integralLinear_coefficient integral_normalizedSectionTensor_eq_modelIntegral integral_normalizedSection_eq_doubleIntegral integral_normalizedSection_eq_modelIntegral integral_right integral_unipotent_mul integrand integrandLinear integrandLinear_apply integrand_normalizedSection integrand_right integrand_unipotent_mul jacquetCoefficientMeasurable jacquetCoefficientTopology jacquetCovarianceBorel jacquetCovarianceLocalField jacquetCovarianceMeasurable jacquetCovarianceSecondCountable jacquetCovarianceSigmaCompact jacquetCovarianceTopology jacquetCovarianceValuativeRel jacquetEvaluationBorel jacquetEvaluationGLBorel jacquetEvaluationGLLocallyCompact jacquetEvaluationGLMeasurable jacquetEvaluationGLSecondCountable jacquetEvaluationLocalField jacquetEvaluationMeasurable jacquetEvaluationNonarchRing jacquetEvaluationT2 jacquetEvaluationTopology jacquetEvaluationValuativeRel jacquetLinearMeasurable jacquetLinearTopology jacquetNonzeroBorel jacquetNonzeroLocalField jacquetNonzeroMeasurable jacquetNonzeroNonarchRing jacquetNonzeroSecondCountable jacquetNonzeroSigmaCompact jacquetNonzeroTopology jacquetNonzeroValuativeRel measurableEmbedding_unipotentShift measurePreserving_unipotentShift modelImageBorel modelImageLocalField modelImageMeasurable modelImageNonarchRing modelImageT2 modelImageTopology modelImageValuative modelIntegral_mem_range_of_fixed_approximation modelIntegral_tmul_mem_range phase_eq_one_neighborhood range_modelIntegral_eq range_modelIntegral_subset range_realTwistIntegralLinear_coefficients_subset realTwistCoefficientMap realTwistCoefficientMap_apply realTwistCoefficientMap_coefficient realTwistIntegralLinear realTwistIntegralLinear_apply realTwistIntegralLinear_coefficient sectionCoefficient sectionCoefficientLinear sectionCoefficientLinear_apply sectionCoefficient_lowerBlock sectionCoefficient_normalizedSection sectionCoefficient_right tensorCoordinates_lowerBlock_action
open Langlands.AllField.RankinSelberg.AdjacentJacquet
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement AdjacentRankModelImageStatement EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneWhittakerTypeStatement SliceIntegrable SliceIntegrableAt TwoBlockJacquetConvergenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement adjacentRankDeterminantWeight adjacentRankDeterminantWeight_apply adjacentRankDeterminantWeight_locallyConstant adjacentRankLowerScalarProjection adjacentRankLower_determinantComplexPower adjacentRankLower_halfModulus adjacentRankLower_weightRatio adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelImage adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_rankOneCutoff exists_rankOneEmbedding_support exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicMatrixFourierSlice padicRectangularHaarScaling padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic functionalsCongr hasCompactSupport_twoBlockCellRestriction mirabolicUnitTest mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker hiding unipotentShift
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open Langlands.RankinSelberg.AdjacentCompactMatrix hiding characterNormExponent characterNormExponent_spec coefficientDeterminantOrder coefficientDeterminantOrder_spec convergenceGLBorel convergenceGLMeasurable convergenceLocalField convergenceMeasurable convergenceNonarchRing convergenceTopology convergenceValuativeRel determinantWeight_add_exponents exists_character_norm_exponent exists_coefficient_det_growth exists_scaled_integral_of_isCompact instIsNonarchimedeanLocalFieldCarrier instTopologicalSpaceCarrier instValuativeRelCarrier integrable_natWeight_of_compact_bound integrable_of_compact_det_growth integrable_realTwist_of_threshold isEntryBounded_of_scaled_integral matrixZeroExtension matrixZeroExtension_apply matrixZeroExtension_of_not_mem_range measurable_matrixZeroExtension norm_realDeterminantWeight norm_realSpectralCharacter norm_realTwistedCharacter pow_ord_mul_abs_pow_le realTwistThreshold realTwistedCharacter transferBorel transferGLBorel transferGLMeasurable transferLocalField transferMeasurable transferSecondCountable transferSigmaCompact transferT2 transferTopology transferValuativeRel uniformizer_pow_ord_div_mem
open Langlands.AllField.RankinSelberg.AdjacentCompactMatrix
open Filter _root_.Topology
open scoped TensorProduct

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance modelImageT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance modelImageNonarchRing : NonarchimedeanRing F := by
  convert! ValuativeRel.nonarchimedeanRing F
  exact Valuation.toTopologicalSpace_eq _
local instance modelImageMeasurable : MeasurableSpace F := borel _
local instance modelImageBorel : BorelSpace F := ⟨rfl⟩
local instance modelImageGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance modelImageGLBorel (n : ℕ) : BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩

variable (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
  (ℓ : glFunctionals ψ r σ) (ν : AdditiveHaarMeasure F)
  (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
  (χ₀ : Quasicharacter F) (u : ℝ)
  (hu : realTwistThreshold F ψ σ hσ ℓ χ₀ < u)

local notation "χᵤ" => realTwistedCharacter F χ₀ u
local notation "ρᵤ" => inducedRepresentation F σ χᵤ

/-- The limit of cutoff-section coefficients belongs to the coefficients of the
same identity integral, using admissibility of the actual original-carrier induction. -/
theorem modelIntegral_mem_range_of_fixed_approximation (hself : IsSelfDual ψ ν)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F))
    (v : V) (J : OpenSubgroup (GeneralLinear (r + 2) F))
    (Ψ : ℕ → adjacentRankCompactTests (r + 1) F)
    (hfixed : ∀ n, Langlands.AllField.RankinSelberg.Padic.adjacentRankNormalizedSection F σ χᵤ hσ.1.1 (Ψ n) v ∈
      fixedVectors ρᵤ J.toSubgroup)
    (hbound : ∀ n M, ‖(Ψ n).val M‖ ≤ ‖Φ M‖)
    (hevent : ∀ M, AdjacentRankFullRank M → ∀ᶠ n in atTop, (Ψ n).val M = Φ M) :
    Langlands.AllField.RankinSelberg.Padic.adjacentRankModelMap F ψ ν hself σ ℓ χᵤ hσ.1.1
      ((partialFourierEquiv ψ ν (r + 1) hself Φ) ⊗ₜ[ℂ] modelMap σ ℓ v) ∈
      Set.range (realTwistCoefficientMap F ψ σ ℓ ν hσ χ₀ u hu) := by
  let L := realTwistIntegralLinear F ψ σ ℓ ν hσ χ₀ u hu 1
  let f (n : ℕ) : fixedVectors ρᵤ J.toSubgroup :=
    ⟨Langlands.AllField.RankinSelberg.Padic.adjacentRankNormalizedSection F σ χᵤ hσ.1.1 (Ψ n) v, hfixed n⟩
  have hlim (g : GeneralLinear (r + 2) F) :
      Tendsto (fun n => L (ρᵤ g (f n).val)) atTop
        (𝓝 (Langlands.AllField.RankinSelberg.Padic.adjacentRankModelMap F ψ ν hself σ ℓ χᵤ hσ.1.1
          ((partialFourierEquiv ψ ν (r + 1) hself Φ) ⊗ₜ[ℂ] modelMap σ ℓ v) g)) := by
    have hd := Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral.tendsto_modelIntegral F ν ψ σ hσ ℓ χ₀ u hu
      (modelMap σ ℓ v) Φ (fun n => (Ψ n).val) hbound hevent hself g
    have heq (n : ℕ) : L (ρᵤ g (f n).val) =
        Langlands.AllField.RankinSelberg.Padic.adjacentRankModelMap F ψ ν hself σ ℓ χᵤ hσ.1.1
          ((partialFourierEquiv ψ ν (r + 1) hself (Ψ n).val) ⊗ₜ[ℂ] modelMap σ ℓ v) g := by
      dsimp only [L, f]
      rw [realTwistIntegralLinear_coefficient]
      exact integral_normalizedSection_eq_modelIntegral F ψ σ ℓ ν hself hσ χ₀ u hu (Ψ n) v g
    simpa only [heq, Langlands.AllField.RankinSelberg.Padic.adjacentRankModelMap_apply, Langlands.AllField.RankinSelberg.Padic.adjacentRankModelIntegral] using hd
  obtain ⟨f₀, hf₀⟩ := mem_range_fixedCoefficientMap_of_tendsto ρᵤ L J
    (Langlands.AllField.RankinSelberg.Padic.adjacentRankNormalizedInduced_isAdmissible F σ χᵤ hσ.1) f _ hlim
  refine ⟨f₀.val, ?_⟩
  funext g
  rw [realTwistCoefficientMap_coefficient]
  exact congrFun hf₀ g

/-- Every whole-function model integral of a pure tensor is a coefficient of the
same identity integral on the actual original-carrier induction. -/
theorem modelIntegral_tmul_mem_range (hself : IsSelfDual ψ ν)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule) :
    Langlands.AllField.RankinSelberg.Padic.adjacentRankModelMap F ψ ν hself σ ℓ χᵤ hσ.1.1 (Φ ⊗ₜ[ℂ] W) ∈
      Set.range (realTwistCoefficientMap F ψ σ ℓ ν hσ χ₀ u hu) := by
  obtain ⟨v, rfl⟩ := modelMap_surjective σ ℓ W
  let Φ₀ := (partialFourierEquiv ψ ν (r + 1) hself).symm Φ
  let A := Langlands.AllField.RankinSelberg.Padic.adjacentRankInvariantApproximation F σ χᵤ hσ.1.1 Φ₀
  have h := modelIntegral_mem_range_of_fixed_approximation F ψ σ ℓ ν hσ χ₀ u hu
    hself Φ₀ v A.level A.tests (fun n => A.fixed n v) A.norm_le A.eventually_eq
  simpa only [Φ₀, LinearEquiv.apply_symm_apply] using h

/-- All finite algebraic test tensors give coefficients of the common integral. -/
theorem range_modelIntegral_subset (hself : IsSelfDual ψ ν) :
    Set.range (Langlands.AllField.RankinSelberg.Padic.adjacentRankModelMap F ψ ν hself σ ℓ χᵤ hσ.1.1) ⊆
      Set.range (realTwistCoefficientMap F ψ σ ℓ ν hσ χ₀ u hu) := by
  rintro _ ⟨t, rfl⟩
  change Langlands.AllField.RankinSelberg.Padic.adjacentRankModelMap F ψ ν hself σ ℓ χᵤ hσ.1.1 t ∈
    LinearMap.range (realTwistCoefficientMap F ψ σ ℓ ν hσ χ₀ u hu)
  induction t using TensorProduct.inductionOn with
  | tmul Φ W =>
    exact modelIntegral_tmul_mem_range F ψ σ ℓ ν hσ χ₀ u hu hself Φ W
  | add a b ha hb =>
    rw [map_add]
    exact Submodule.add_mem _ ha hb

/-- Whole-function range equality at the original uniform twist threshold. -/
theorem range_modelIntegral_eq (hself : IsSelfDual ψ ν) :
    Set.range (Langlands.AllField.RankinSelberg.Padic.adjacentRankModelMap F ψ ν hself σ ℓ χᵤ hσ.1.1) =
      Set.range (realTwistCoefficientMap F ψ σ ℓ ν hσ χ₀ u hu) := by
  apply Set.Subset.antisymm
  · exact range_modelIntegral_subset F ψ σ ℓ ν hσ χ₀ u hu hself
  · have heq : (fun f => fun g => realTwistIntegralLinear F ψ σ ℓ ν hσ χ₀ u hu 1
        (ρᵤ g f)) = realTwistCoefficientMap F ψ σ ℓ ν hσ χ₀ u hu := by
      funext f g
      exact (realTwistCoefficientMap_coefficient F ψ σ ℓ ν hσ χ₀ u hu f g).symm
    rw [← heq]
    exact range_realTwistIntegralLinear_coefficients_subset F ψ σ ℓ ν hσ χ₀ u hu hself

end Langlands.AllField.RankinSelberg.AdjacentJacquet

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement AdjacentRankModelImageStatement EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneWhittakerTypeStatement SliceIntegrable SliceIntegrableAt TwoBlockJacquetConvergenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement adjacentRankDeterminantWeight adjacentRankDeterminantWeight_apply adjacentRankDeterminantWeight_locallyConstant adjacentRankLowerScalarProjection adjacentRankLower_determinantComplexPower adjacentRankLower_halfModulus adjacentRankLower_weightRatio adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelImage adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_rankOneCutoff exists_rankOneEmbedding_support exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicMatrixFourierSlice padicRectangularHaarScaling padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic functionalsCongr hasCompactSupport_twoBlockCellRestriction mirabolicUnitTest mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.RankinSelberg.AdjacentCompactMatrix hiding characterNormExponent characterNormExponent_spec coefficientDeterminantOrder coefficientDeterminantOrder_spec convergenceGLBorel convergenceGLMeasurable convergenceLocalField convergenceMeasurable convergenceNonarchRing convergenceTopology convergenceValuativeRel determinantWeight_add_exponents exists_character_norm_exponent exists_coefficient_det_growth exists_scaled_integral_of_isCompact instIsNonarchimedeanLocalFieldCarrier instTopologicalSpaceCarrier instValuativeRelCarrier integrable_natWeight_of_compact_bound integrable_of_compact_det_growth integrable_realTwist_of_threshold isEntryBounded_of_scaled_integral matrixZeroExtension matrixZeroExtension_apply matrixZeroExtension_of_not_mem_range measurable_matrixZeroExtension norm_realDeterminantWeight norm_realSpectralCharacter norm_realTwistedCharacter pow_ord_mul_abs_pow_le realTwistThreshold realTwistedCharacter transferBorel transferGLBorel transferGLMeasurable transferLocalField transferMeasurable transferSecondCountable transferSigmaCompact transferT2 transferTopology transferValuativeRel uniformizer_pow_ord_div_mem
open Langlands.AllField.RankinSelberg.AdjacentCompactMatrix
open Langlands.RankinSelberg.AdjacentJacquet hiding compactTestModelTensor compactTestModelTensor_tmul determinantWeight_eq exists_constantKernel_section functional functional_coefficient functional_ne_zero inducedRepresentation inducing_isSmooth instBorelSpaceCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instTotallyDisconnectedSpaceCarrier instValuativeRelCarrier integrable_normalizedSection_realTwist integrable_realTwist integral integralLinear integralLinear_apply integralLinear_coefficient integral_normalizedSectionTensor_eq_modelIntegral integral_normalizedSection_eq_doubleIntegral integral_normalizedSection_eq_modelIntegral integral_right integral_unipotent_mul integrand integrandLinear integrandLinear_apply integrand_normalizedSection integrand_right integrand_unipotent_mul jacquetCoefficientMeasurable jacquetCoefficientTopology jacquetCovarianceBorel jacquetCovarianceLocalField jacquetCovarianceMeasurable jacquetCovarianceSecondCountable jacquetCovarianceSigmaCompact jacquetCovarianceTopology jacquetCovarianceValuativeRel jacquetEvaluationBorel jacquetEvaluationGLBorel jacquetEvaluationGLLocallyCompact jacquetEvaluationGLMeasurable jacquetEvaluationGLSecondCountable jacquetEvaluationLocalField jacquetEvaluationMeasurable jacquetEvaluationNonarchRing jacquetEvaluationT2 jacquetEvaluationTopology jacquetEvaluationValuativeRel jacquetLinearMeasurable jacquetLinearTopology jacquetNonzeroBorel jacquetNonzeroLocalField jacquetNonzeroMeasurable jacquetNonzeroNonarchRing jacquetNonzeroSecondCountable jacquetNonzeroSigmaCompact jacquetNonzeroTopology jacquetNonzeroValuativeRel measurableEmbedding_unipotentShift measurePreserving_unipotentShift modelImageBorel modelImageLocalField modelImageMeasurable modelImageNonarchRing modelImageT2 modelImageTopology modelImageValuative modelIntegral_mem_range_of_fixed_approximation modelIntegral_tmul_mem_range phase_eq_one_neighborhood range_modelIntegral_eq range_modelIntegral_subset range_realTwistIntegralLinear_coefficients_subset realTwistCoefficientMap realTwistCoefficientMap_apply realTwistCoefficientMap_coefficient realTwistIntegralLinear realTwistIntegralLinear_apply realTwistIntegralLinear_coefficient sectionCoefficient sectionCoefficientLinear sectionCoefficientLinear_apply sectionCoefficient_lowerBlock sectionCoefficient_normalizedSection sectionCoefficient_right tensorCoordinates_lowerBlock_action
open Langlands.AllField.RankinSelberg.AdjacentJacquet

/-- The full JPSS adjacent-rank model image is the coefficient image of one
nonzero standard Whittaker functional on the actual normalized lower induction. -/
theorem adjacentRankModelImage.{uF,uV} : AdjacentRankModelImageStatement.{uF,uV} := by
  intro F _ _ _ _
  let : MeasurableSpace F := borel _
  have : BorelSpace F := ⟨rfl⟩
  have : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
  have : TotallyDisconnectedSpace F := by
    let : NonarchimedeanRing F := by
      convert! ValuativeRel.nonarchimedeanRing F
      exact Valuation.toTopologicalSpace_eq _
    infer_instance
  intro ψ ν hself r V _ _ σ hσ ℓ hℓ χ₀
  refine ⟨realTwistThreshold F ψ σ hσ ℓ χ₀, ?_⟩
  intro u hu
  let χᵤ := realTwistedCharacter F χ₀ u
  let hI := integrable_realTwist F ψ σ ℓ ν hσ χ₀ u hu
  refine ⟨functional F ψ σ ℓ χᵤ ν hI,
    functional_ne_zero F ψ σ ℓ χᵤ ν hσ.1.1 hℓ hI, ?_⟩
  change Set.range (Langlands.AllField.RankinSelberg.Padic.adjacentRankModelMap F ψ ν hself σ ℓ χᵤ hσ.1.1) = _
  rw [range_modelIntegral_eq F ψ σ ℓ ν hσ χ₀ u hu hself]
  congr 1
  funext f g
  exact (functional_coefficient F ψ σ ℓ χᵤ ν hI f g).symm

end Langlands.AllField.RankinSelberg
