import Langlands.Representation.RankinSelberg.AdjacentRankJacquetIntegrability
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankJacquetLinear
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankModelMap
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankSectionSurjectivity
/-! All-section convergence and coefficient containment for the actual induction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllField.RankinSelberg.AdjacentJacquet
open Langlands.RankinSelberg.AdjacentJacquet hiding compactTestModelTensor compactTestModelTensor_tmul determinantWeight_eq inducedRepresentation instBorelSpaceCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instTotallyDisconnectedSpaceCarrier instValuativeRelCarrier integrable_normalizedSection_realTwist integrable_realTwist integral integralLinear integralLinear_apply integralLinear_coefficient integral_normalizedSectionTensor_eq_modelIntegral integral_normalizedSection_eq_doubleIntegral integral_normalizedSection_eq_modelIntegral integral_right integrand integrandLinear integrandLinear_apply integrand_normalizedSection integrand_right jacquetEvaluationBorel jacquetEvaluationGLBorel jacquetEvaluationGLLocallyCompact jacquetEvaluationGLMeasurable jacquetEvaluationGLSecondCountable jacquetEvaluationLocalField jacquetEvaluationMeasurable jacquetEvaluationNonarchRing jacquetEvaluationT2 jacquetEvaluationTopology jacquetEvaluationValuativeRel jacquetLinearMeasurable jacquetLinearTopology range_realTwistIntegralLinear_coefficients_subset realTwistIntegralLinear realTwistIntegralLinear_apply realTwistIntegralLinear_coefficient sectionCoefficient sectionCoefficientLinear sectionCoefficientLinear_apply sectionCoefficient_normalizedSection sectionCoefficient_right
open Langlands.AllField.RankinSelberg.AdjacentJacquet
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneWhittakerTypeStatement SliceIntegrable SliceIntegrableAt TwoBlockJacquetConvergenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement adjacentRankDeterminantWeight adjacentRankDeterminantWeight_apply adjacentRankDeterminantWeight_locallyConstant adjacentRankLowerScalarProjection adjacentRankLower_determinantComplexPower adjacentRankLower_halfModulus adjacentRankLower_weightRatio adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_rankOneCutoff exists_rankOneEmbedding_support exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicMatrixFourierSlice padicRectangularHaarScaling padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic functionalsCongr hasCompactSupport_twoBlockCellRestriction mirabolicUnitTest mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.RankinSelberg.AdjacentCompactMatrix hiding characterNormExponent characterNormExponent_spec coefficientDeterminantOrder coefficientDeterminantOrder_spec convergenceGLBorel convergenceGLMeasurable convergenceLocalField convergenceMeasurable convergenceNonarchRing convergenceTopology convergenceValuativeRel determinantWeight_add_exponents exists_character_norm_exponent exists_coefficient_det_growth exists_scaled_integral_of_isCompact instIsNonarchimedeanLocalFieldCarrier instTopologicalSpaceCarrier instValuativeRelCarrier integrable_natWeight_of_compact_bound integrable_of_compact_det_growth integrable_realTwist_of_threshold isEntryBounded_of_scaled_integral matrixZeroExtension matrixZeroExtension_apply matrixZeroExtension_of_not_mem_range measurable_matrixZeroExtension norm_realDeterminantWeight norm_realSpectralCharacter norm_realTwistedCharacter pow_ord_mul_abs_pow_le realTwistThreshold realTwistedCharacter transferBorel transferGLBorel transferGLMeasurable transferLocalField transferMeasurable transferSecondCountable transferSigmaCompact transferT2 transferTopology transferValuativeRel uniformizer_pow_ord_div_mem
open Langlands.AllField.RankinSelberg.AdjacentCompactMatrix
open scoped TensorProduct

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance : MeasurableSpace F := borel _
local instance : BorelSpace F := ⟨rfl⟩

variable (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
  (ℓ : glFunctionals ψ r σ) (ν : AdditiveHaarMeasure F)
  (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
  (χ₀ : Quasicharacter F) (u : ℝ)
  (hu : Langlands.AllField.RankinSelberg.AdjacentCompactMatrix.realTwistThreshold F ψ σ hσ ℓ χ₀ < u)

include hσ hu in
/-- The same representation-uniform real-twist threshold makes the literal
Jacquet kernel integrable for every actual induced section and every translate. -/
theorem integrable_realTwist
    (f : (inducedRepresentation F σ (realTwistedCharacter F χ₀ u)).asModule)
    (g : GeneralLinear (r + 2) F) :
    Integrable (integrand F ψ σ ℓ (realTwistedCharacter F χ₀ u) f g)
      (rowMeasure ν (r + 1)) := by
  obtain ⟨t, rfl⟩ := Langlands.AllField.RankinSelberg.Padic.adjacentRankNormalizedSectionTensor_surjective
    F σ (realTwistedCharacter F χ₀ u) hσ.1.1 f
  induction t using TensorProduct.inductionOn with
  | tmul Φ v =>
    exact integrable_normalizedSection_realTwist F ψ σ ℓ ν hσ χ₀ u hu Φ v g
  | add a b ha hb =>
    have hadd : integrand F ψ σ ℓ (realTwistedCharacter F χ₀ u)
        (Langlands.AllField.RankinSelberg.Padic.adjacentRankNormalizedSectionTensor F σ
          (realTwistedCharacter F χ₀ u) hσ.1.1 (a + b)) g =
        integrand F ψ σ ℓ (realTwistedCharacter F χ₀ u)
          (Langlands.AllField.RankinSelberg.Padic.adjacentRankNormalizedSectionTensor F σ
            (realTwistedCharacter F χ₀ u) hσ.1.1 a) g +
        integrand F ψ σ ℓ (realTwistedCharacter F χ₀ u)
          (Langlands.AllField.RankinSelberg.Padic.adjacentRankNormalizedSectionTensor F σ
            (realTwistedCharacter F χ₀ u) hσ.1.1 b) g := by
      rw [map_add]
      exact (integrandLinear F ψ σ ℓ (realTwistedCharacter F χ₀ u) g).map_add
        _ _ |>.trans (by rfl)
    rw [hadd]
    exact ha.add hb

/-- The literal integral at any ambient element, with convergence discharged
on the exact original-carrier normalized opposite induction. -/
def realTwistIntegralLinear (g : GeneralLinear (r + 2) F) :
    (inducedRepresentation F σ (realTwistedCharacter F χ₀ u)).asModule →ₗ[ℂ] ℂ :=
  integralLinear F ψ σ ℓ (realTwistedCharacter F χ₀ u) ν
    (integrable_realTwist F ψ σ ℓ ν hσ χ₀ u hu) g

@[simp] theorem realTwistIntegralLinear_apply
    (g : GeneralLinear (r + 2) F)
    (f : (inducedRepresentation F σ (realTwistedCharacter F χ₀ u)).asModule) :
    realTwistIntegralLinear F ψ σ ℓ ν hσ χ₀ u hu g f =
      integral F ψ σ ℓ (realTwistedCharacter F χ₀ u) ν f g := rfl

/-- Every coefficient of the identity integral is the literal integral at g. -/
theorem realTwistIntegralLinear_coefficient
    (f : (inducedRepresentation F σ (realTwistedCharacter F χ₀ u)).asModule)
    (g : GeneralLinear (r + 2) F) :
    realTwistIntegralLinear F ψ σ ℓ ν hσ χ₀ u hu 1
      (inducedRepresentation F σ (realTwistedCharacter F χ₀ u) g f) =
      integral F ψ σ ℓ (realTwistedCharacter F χ₀ u) ν f g :=
  integralLinear_coefficient F ψ σ ℓ (realTwistedCharacter F χ₀ u) ν
    (integrable_realTwist F ψ σ ℓ ν hσ χ₀ u hu) f g

/-- The compact-test tensor maps into the whole model test space by the
specified partial Fourier transform and the original coefficient quotient. -/
def compactTestModelTensor (hself : IsSelfDual ψ ν) :
    TensorProduct ℂ (adjacentRankCompactTests (r + 1) F) V →ₗ[ℂ]
      adjacentRankTestSpace ψ σ ℓ :=
  TensorProduct.map
    ((partialFourierEquiv ψ ν (r + 1) hself).toLinearMap.comp
      (adjacentRankCompactTests (r + 1) F).subtype)
    (modelMap σ ℓ).toLinearMap

@[simp] theorem compactTestModelTensor_tmul (hself : IsSelfDual ψ ν)
    (Φ : adjacentRankCompactTests (r + 1) F) (v : V) :
    compactTestModelTensor F ψ σ ℓ ν hself (Φ ⊗ₜ[ℂ] v) =
      (partialFourierEquiv ψ ν (r + 1) hself Φ.val) ⊗ₜ[ℂ] (modelMap σ ℓ v) := rfl

include hu in
/-- Exact comparison on the entire compact-test/original-vector tensor product. -/
theorem integral_normalizedSectionTensor_eq_modelIntegral (hself : IsSelfDual ψ ν)
    (t : TensorProduct ℂ (adjacentRankCompactTests (r + 1) F) V) :
    (fun g => integral F ψ σ ℓ (realTwistedCharacter F χ₀ u) ν
      (Langlands.AllField.RankinSelberg.Padic.adjacentRankNormalizedSectionTensor F σ
        (realTwistedCharacter F χ₀ u) hσ.1.1 t) g) =
    Langlands.AllField.RankinSelberg.Padic.adjacentRankModelMap F ψ ν hself σ ℓ
      (realTwistedCharacter F χ₀ u) hσ.1.1
      (compactTestModelTensor F ψ σ ℓ ν hself t) := by
  induction t using TensorProduct.inductionOn with
  | tmul Φ v =>
    funext g
    exact integral_normalizedSection_eq_modelIntegral F ψ σ ℓ ν hself
      hσ χ₀ u hu Φ v g
  | add a b ha hb =>
    funext g
    change realTwistIntegralLinear F ψ σ ℓ ν hσ χ₀ u hu g
      (Langlands.AllField.RankinSelberg.Padic.adjacentRankNormalizedSectionTensor F σ
        (realTwistedCharacter F χ₀ u) hσ.1.1 (a + b)) = _
    simp only [map_add, Pi.add_apply]
    exact congrFun ha g ▸ congrFun hb g ▸ rfl

/-- Every coefficient of the common integral belongs to the whole model image.
The reverse inclusion, for all Schwartz tests, is a separate obligation. -/
theorem range_realTwistIntegralLinear_coefficients_subset (hself : IsSelfDual ψ ν) :
    Set.range (fun f => fun g => realTwistIntegralLinear F ψ σ ℓ ν hσ χ₀ u hu 1
      (inducedRepresentation F σ (realTwistedCharacter F χ₀ u) g f)) ⊆
    Set.range (Langlands.AllField.RankinSelberg.Padic.adjacentRankModelMap F ψ ν hself σ ℓ
      (realTwistedCharacter F χ₀ u) hσ.1.1) := by
  rintro _ ⟨f, rfl⟩
  obtain ⟨t, rfl⟩ := Langlands.AllField.RankinSelberg.Padic.adjacentRankNormalizedSectionTensor_surjective
    F σ (realTwistedCharacter F χ₀ u) hσ.1.1 f
  refine ⟨compactTestModelTensor F ψ σ ℓ ν hself t, ?_⟩
  rw [← integral_normalizedSectionTensor_eq_modelIntegral F ψ σ ℓ ν hσ χ₀ u hu hself t]
  funext g
  exact (realTwistIntegralLinear_coefficient F ψ σ ℓ ν hσ χ₀ u hu _ g).symm

end Langlands.AllField.RankinSelberg.AdjacentJacquet
