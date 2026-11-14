import Langlands.Representation.RankinSelberg.AdjacentRankJacquetLimit
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankJacquetIntegrability
/-! Pointwise model convergence for norm-bounded full-rank Schwartz approximations. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneWhittakerTypeStatement SliceIntegrable SliceIntegrableAt TwoBlockJacquetConvergenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement adjacentRankDeterminantWeight adjacentRankDeterminantWeight_apply adjacentRankDeterminantWeight_locallyConstant adjacentRankLowerScalarProjection adjacentRankLower_determinantComplexPower adjacentRankLower_halfModulus adjacentRankLower_weightRatio adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_rankOneCutoff exists_rankOneEmbedding_support exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicMatrixFourierSlice padicRectangularHaarScaling padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic functionalsCongr hasCompactSupport_twoBlockCellRestriction mirabolicUnitTest mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open Langlands.RankinSelberg.AdjacentCompactMatrix hiding characterNormExponent characterNormExponent_spec coefficientDeterminantOrder coefficientDeterminantOrder_spec convergenceGLBorel convergenceGLMeasurable convergenceLocalField convergenceMeasurable convergenceNonarchRing convergenceTopology convergenceValuativeRel determinantWeight_add_exponents exists_character_norm_exponent exists_coefficient_det_growth exists_scaled_integral_of_isCompact instIsNonarchimedeanLocalFieldCarrier instTopologicalSpaceCarrier instValuativeRelCarrier integrable_natWeight_of_compact_bound integrable_of_compact_det_growth integrable_realTwist_of_threshold isEntryBounded_of_scaled_integral matrixZeroExtension matrixZeroExtension_apply matrixZeroExtension_of_not_mem_range measurable_matrixZeroExtension norm_realDeterminantWeight norm_realSpectralCharacter norm_realTwistedCharacter pow_ord_mul_abs_pow_le realTwistThreshold realTwistedCharacter transferBorel transferGLBorel transferGLMeasurable transferLocalField transferMeasurable transferSecondCountable transferSigmaCompact transferT2 transferTopology transferValuativeRel uniformizer_pow_ord_div_mem
open Langlands.AllField.RankinSelberg.AdjacentCompactMatrix
open Filter _root_.Topology Matrix
open scoped TensorProduct

universe uF uV

section Rank


end Rank

namespace AdjacentDoubleIntegral
open Langlands.RankinSelberg.AdjacentDoubleIntegral hiding columnHomeomorph columnHomeomorph_apply continuous_integrand doubleIntegralBorel doubleIntegralGLBorel doubleIntegralGLLocallyCompact doubleIntegralGLMeasurable doubleIntegralGLSecondCountable doubleIntegralLocalField doubleIntegralMeasurable doubleIntegralNonarchRing doubleIntegralSecondCountable doubleIntegralSigmaCompact doubleIntegralT2 doubleIntegralTopology doubleIntegralValuativeRel double_integral_eq_modelIntegral double_integral_eq_modelIntegrand double_integral_eq_partialFourier fiberNorm fiberNorm_apply integrable_column integrable_realTwist integral_column_partialFourier integral_mulVec integral_norm_column integrand jacobian_detWeight jacquetLimitBorel jacquetLimitGLBorel jacquetLimitGLLocallyCompact jacquetLimitGLMeasurable jacquetLimitGLSecondCountable jacquetLimitLocalField jacquetLimitMeasurable jacquetLimitNonarchRing jacquetLimitSecondCountable jacquetLimitT2 jacquetLimitTopology jacquetLimitValuative norm_fiberNorm_apply rowMeasure_map_mulVec tendsto_doubleIntegral tendsto_modelIntegral
open Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneWhittakerTypeStatement SliceIntegrable SliceIntegrableAt TwoBlockJacquetConvergenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement adjacentRankDeterminantWeight adjacentRankDeterminantWeight_apply adjacentRankDeterminantWeight_locallyConstant adjacentRankLowerScalarProjection adjacentRankLower_determinantComplexPower adjacentRankLower_halfModulus adjacentRankLower_weightRatio adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_rankOneCutoff exists_rankOneEmbedding_support exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance jacquetLimitT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance jacquetLimitNonarchRing : NonarchimedeanRing F := by
  convert! ValuativeRel.nonarchimedeanRing F
  exact Valuation.toTopologicalSpace_eq _
local instance jacquetLimitSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance jacquetLimitMeasurable : MeasurableSpace F := borel _
local instance jacquetLimitBorel : BorelSpace F := ⟨rfl⟩
local instance jacquetLimitGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance jacquetLimitGLBorel (n : ℕ) : BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance jacquetLimitGLLocallyCompact (n : ℕ) : LocallyCompactSpace (GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace (n + 1)
local instance jacquetLimitGLSecondCountable (n : ℕ) : SecondCountableTopology (GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology (n + 1)

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

variable (ν : AdditiveHaarMeasure F) (ψ : UnitaryAdditiveCharacter F)
  {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
  (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (ℓ : glFunctionals ψ r σ)
  (χ₀ : Quasicharacter F) (u : ℝ)
  (hu : realTwistThreshold F ψ σ hσ ℓ χ₀ < u)
  (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
  (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F))
  (Ψ : ℕ → SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F))
  (hbound : ∀ n M, ‖Ψ n M‖ ≤ ‖Φ M‖)
  (hevent : ∀ M, AdjacentRankFullRank M → ∀ᶠ n in atTop, Ψ n M = Φ M)

include hσ hu hbound hevent in
/-- Dominated convergence on the genuine row-times-matrix measure, followed by
Fubini, for every ambient translate of the whole Schwartz test. -/
theorem tendsto_doubleIntegral (g : GeneralLinear (r + 2) F) :
    Tendsto (fun n => ∫ x, ∫ h, integrand F ψ σ ℓ (realTwistedCharacter F χ₀ u)
      (rectangularTranslate g (Ψ n)) W x h
        ∂generalLinearHaar F r ∂rowMeasure ν (r + 1)) atTop
      (𝓝 (∫ x, ∫ h, integrand F ψ σ ℓ (realTwistedCharacter F χ₀ u)
        (rectangularTranslate g Φ) W x h
          ∂generalLinearHaar F r ∂rowMeasure ν (r + 1))) := by
  let K (Ξ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F))
      (z : (Fin (r + 1) → F) × GeneralLinear (r + 1) F) :=
    integrand F ψ σ ℓ (realTwistedCharacter F χ₀ u) (rectangularTranslate g Ξ) W z.1 z.2
  have hi (Ξ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F)) :
      Integrable (K Ξ) ((rowMeasure ν (r + 1)).prod (generalLinearHaar F r)) :=
    integrable_realTwist F ν ψ σ hσ ℓ χ₀ u hu W (rectangularTranslate g Ξ)
  have hd := tendsto_integral_of_dominated_convergence (f := K Φ) (fun z => ‖K Φ z‖)
    (fun n => (hi (Ψ n)).aestronglyMeasurable) (hi Φ).norm
    (fun n => Filter.Eventually.of_forall fun z => ?_) (Filter.Eventually.of_forall fun z => ?_)
  · simpa only [integral_prod _ (hi _)] using hd
  · dsimp only [K, integrand, rectangularTranslate_apply]
    simp only [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hbound n _) (norm_nonneg _)) (norm_nonneg _))
        (norm_nonneg _)) (norm_nonneg _)
  · apply tendsto_const_nhds.congr'
    filter_upwards [hevent _ (adjacentRankFullRank_doubleKernel z.2 z.1 g)] with n hn
    dsimp only [K, integrand, rectangularTranslate_apply]
    rw [hn]

include hσ hu hbound hevent in
/-- The actual model integrals of the partial Fourier transforms converge
pointwise, with the original threshold and supplied Haar normalization. -/
theorem tendsto_modelIntegral (hself : IsSelfDual ψ ν)
    (g : GeneralLinear (r + 2) F) :
    Tendsto (fun n => adjacentRankModelIntegral ψ ν hself σ ℓ abv
      (realTwistedCharacter F χ₀ u) (generalLinearHaar F r)
      ((partialFourierEquiv ψ ν (r + 1) hself (Ψ n)) ⊗ₜ[ℂ] W) g) atTop
      (𝓝 (adjacentRankModelIntegral ψ ν hself σ ℓ abv
        (realTwistedCharacter F χ₀ u) (generalLinearHaar F r)
        ((partialFourierEquiv ψ ν (r + 1) hself Φ) ⊗ₜ[ℂ] W) g)) := by
  simp_rw [← double_integral_eq_modelIntegral F ν ψ hself σ hσ ℓ χ₀ u hu W]
  exact (tendsto_doubleIntegral F ν ψ σ hσ ℓ χ₀ u hu W Φ Ψ hbound hevent g).const_mul _

end AdjacentDoubleIntegral

namespace AdjacentJacquet
open Langlands.RankinSelberg.AdjacentJacquet hiding compactTestModelTensor compactTestModelTensor_tmul determinantWeight_eq inducedRepresentation instBorelSpaceCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instTotallyDisconnectedSpaceCarrier instValuativeRelCarrier integrable_normalizedSection_realTwist integrable_realTwist integral integralLinear integralLinear_apply integralLinear_coefficient integral_normalizedSectionTensor_eq_modelIntegral integral_normalizedSection_eq_doubleIntegral integral_normalizedSection_eq_modelIntegral integral_right integrand integrandLinear integrandLinear_apply integrand_normalizedSection integrand_right jacquetCoefficientMeasurable jacquetCoefficientTopology jacquetEvaluationBorel jacquetEvaluationGLBorel jacquetEvaluationGLLocallyCompact jacquetEvaluationGLMeasurable jacquetEvaluationGLSecondCountable jacquetEvaluationLocalField jacquetEvaluationMeasurable jacquetEvaluationNonarchRing jacquetEvaluationT2 jacquetEvaluationTopology jacquetEvaluationValuativeRel jacquetLinearMeasurable jacquetLinearTopology range_realTwistIntegralLinear_coefficients_subset realTwistCoefficientMap realTwistCoefficientMap_apply realTwistCoefficientMap_coefficient realTwistIntegralLinear realTwistIntegralLinear_apply realTwistIntegralLinear_coefficient sectionCoefficient sectionCoefficientLinear sectionCoefficientLinear_apply sectionCoefficient_normalizedSection sectionCoefficient_right
open Langlands.AllField.RankinSelberg.AdjacentJacquet
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneWhittakerTypeStatement SliceIntegrable SliceIntegrableAt TwoBlockJacquetConvergenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement adjacentRankDeterminantWeight adjacentRankDeterminantWeight_apply adjacentRankDeterminantWeight_locallyConstant adjacentRankLowerScalarProjection adjacentRankLower_determinantComplexPower adjacentRankLower_halfModulus adjacentRankLower_weightRatio adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_rankOneCutoff exists_rankOneEmbedding_support exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance jacquetCoefficientMeasurable : MeasurableSpace F := borel _

variable (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
  (ℓ : glFunctionals ψ r σ) (ν : AdditiveHaarMeasure F)
  (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
  (χ₀ : Quasicharacter F) (u : ℝ)
  (hu : realTwistThreshold F ψ σ hσ ℓ χ₀ < u)

/-- All coefficients of the one identity Jacquet integral as a scalar linear map. -/
def realTwistCoefficientMap :
    (inducedRepresentation F σ (realTwistedCharacter F χ₀ u)).asModule →ₗ[ℂ]
      (GeneralLinear (r + 2) F → ℂ) where
  toFun f g := realTwistIntegralLinear F ψ σ ℓ ν hσ χ₀ u hu g f
  map_add' f f' := by
    funext g
    exact (realTwistIntegralLinear F ψ σ ℓ ν hσ χ₀ u hu g).map_add f f'
  map_smul' c f := by
    funext g
    exact (realTwistIntegralLinear F ψ σ ℓ ν hσ χ₀ u hu g).map_smul c f

@[simp] theorem realTwistCoefficientMap_apply
    (f : (inducedRepresentation F σ (realTwistedCharacter F χ₀ u)).asModule)
    (g : GeneralLinear (r + 2) F) :
    realTwistCoefficientMap F ψ σ ℓ ν hσ χ₀ u hu f g =
      integral F ψ σ ℓ (realTwistedCharacter F χ₀ u) ν f g :=
  rfl

/-- This linear map consists of coefficients of one fixed identity integral. -/
theorem realTwistCoefficientMap_coefficient
    (f : (inducedRepresentation F σ (realTwistedCharacter F χ₀ u)).asModule)
    (g : GeneralLinear (r + 2) F) :
    realTwistCoefficientMap F ψ σ ℓ ν hσ χ₀ u hu f g =
      realTwistIntegralLinear F ψ σ ℓ ν hσ χ₀ u hu 1
        (inducedRepresentation F σ (realTwistedCharacter F χ₀ u) g f) :=
  (realTwistIntegralLinear_coefficient F ψ σ ℓ ν hσ χ₀ u hu f g).symm

end AdjacentJacquet

end Langlands.AllField.RankinSelberg
