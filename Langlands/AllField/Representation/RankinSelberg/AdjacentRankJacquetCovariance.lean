import Langlands.Representation.RankinSelberg.AdjacentRankJacquetCovariance
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankJacquetLinear
/-! Standard Whittaker covariance for the actual adjacent lower Jacquet integral. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Matrix
open scoped BigOperators

namespace Langlands.AllField.RankinSelberg.AdjacentJacquet
open Langlands.RankinSelberg.AdjacentJacquet hiding determinantWeight_eq functional functional_coefficient inducedRepresentation integrable_normalizedSection_realTwist integral integralLinear integralLinear_apply integralLinear_coefficient integral_normalizedSection_eq_doubleIntegral integral_normalizedSection_eq_modelIntegral integral_right integral_unipotent_mul integrand integrandLinear integrandLinear_apply integrand_normalizedSection integrand_right integrand_unipotent_mul jacquetCovarianceBorel jacquetCovarianceLocalField jacquetCovarianceMeasurable jacquetCovarianceSecondCountable jacquetCovarianceSigmaCompact jacquetCovarianceTopology jacquetCovarianceValuativeRel jacquetEvaluationBorel jacquetEvaluationGLBorel jacquetEvaluationGLLocallyCompact jacquetEvaluationGLMeasurable jacquetEvaluationGLSecondCountable jacquetEvaluationLocalField jacquetEvaluationMeasurable jacquetEvaluationNonarchRing jacquetEvaluationT2 jacquetEvaluationTopology jacquetEvaluationValuativeRel jacquetLinearMeasurable jacquetLinearTopology measurableEmbedding_unipotentShift measurePreserving_unipotentShift sectionCoefficient sectionCoefficientLinear sectionCoefficientLinear_apply sectionCoefficient_lowerBlock sectionCoefficient_normalizedSection sectionCoefficient_right tensorCoordinates_lowerBlock_action
open Langlands.AllField.RankinSelberg.AdjacentJacquet
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneWhittakerTypeStatement SliceIntegrable SliceIntegrableAt TwoBlockJacquetConvergenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement adjacentRankDeterminantWeight adjacentRankDeterminantWeight_apply adjacentRankDeterminantWeight_locallyConstant adjacentRankLowerScalarProjection adjacentRankLower_determinantComplexPower adjacentRankLower_halfModulus adjacentRankLower_weightRatio adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_rankOneCutoff exists_rankOneEmbedding_support exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicMatrixFourierSlice padicRectangularHaarScaling padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic functionalsCongr hasCompactSupport_twoBlockCellRestriction mirabolicUnitTest mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker hiding unipotentShift

universe uF uV

section Algebra


end Algebra

section Padic

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance jacquetCovarianceSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance jacquetCovarianceSigmaCompact : SigmaCompactSpace F :=
  (⟨⟩ : LocalFieldData F).sigmaCompactSpace
local instance jacquetCovarianceMeasurable : MeasurableSpace F := borel _
local instance jacquetCovarianceBorel : BorelSpace F := ⟨rfl⟩

variable {r : ℕ}

/-- The affine unipotent substitution preserves the supplied additive row Haar. -/
theorem measurePreserving_unipotentShift (ν : AdditiveHaarMeasure F)
    (n : upperUnipotent (r + 2) F) :
    MeasurePreserving (unipotentShift n) (rowMeasure ν (r + 1))
      (rowMeasure ν (r + 1)) := by
  have he : unipotentShift n =
      Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral.columnHomeomorph F (unipotentHead n)⁻¹ ∘
        (Homeomorph.addRight (unipotentColumn n)) := rfl
  rw [he]
  refine MeasurePreserving.comp
    ⟨(Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral.columnHomeomorph F _).continuous.measurable, ?_⟩
    (measurePreserving_add_right _ _)
  change (rowMeasure ν (r + 1)).map (fun x => ((unipotentHead n)⁻¹).val *ᵥ x) = _
  rw [Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral.rowMeasure_map_mulVec F ν,
    unipotent_det ⟨_, inv_mem (unipotentHead_mem n)⟩, map_one, inv_one, one_smul]

/-- The same literal substitution is a measurable embedding. -/
theorem measurableEmbedding_unipotentShift
    (n : upperUnipotent (r + 2) F) :
    MeasurableEmbedding (unipotentShift n) :=
  (Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral.columnHomeomorph F _).measurableEmbedding.comp
    (Homeomorph.addRight _).measurableEmbedding

variable (ψ : UnitaryAdditiveCharacter F)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
  (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F)

local notation "ρ" => inducedRepresentation F σ χ

/-- The lower normalized inducing action is exactly σ(a) on a unipotent
head block: both determinant weights are one. -/
theorem tensorCoordinates_lowerBlock_action
    (a : upperUnipotent (r + 1) F)
    (z : PiTensorProduct ℂ (Shahidi.pairCarrier V (ULift.{uV} ℂ))) :
    adjacentRankLowerTensorCoordinates V
      (Langlands.AllField.RankinSelberg.Padic.adjacentRankLowerTensorRepresentation F σ χ (lowerBlockParabolic a.val) z) =
        σ a.val (adjacentRankLowerTensorCoordinates V z) := by
  have he := LinearMap.congr_fun
    ((Langlands.AllField.RankinSelberg.Padic.adjacentRankLowerInducingCoordinates F σ χ).isIntertwining'
      (lowerBlockParabolic a.val)) z
  change adjacentRankLowerTensorCoordinates V
      (Langlands.AllField.RankinSelberg.Padic.adjacentRankLowerTensorRepresentation F σ χ (lowerBlockParabolic a.val) z) =
    Langlands.AllField.RankinSelberg.Padic.adjacentRankLowerCompactRepresentation F σ χ (lowerBlockParabolic a.val)
      (adjacentRankLowerTensorCoordinates V z) at he
  rw [he]
  have hd : GeneralLinear.determinant a.val = 1 := Units.ext (unipotent_det a)
  have hb : GeneralLinear.determinant (lowerBlock a.val) = 1 :=
    Units.ext (unipotent_det ⟨_, lowerBlock_mem a⟩)
  change (((adjacentRankDeterminantWeight (⟨⟩ : LocalFieldData F) χ
      (r + 2) ((r + 1 : ℕ) / 2)).toMonoidHom (lowerBlock a.val) *
        ((adjacentRankDeterminantWeight (⟨⟩ : LocalFieldData F) χ
          (r + 1) ((r + 2 : ℕ) / 2)).toMonoidHom
            (adjacentRankLowerLargeProjection (lowerBlockParabolic a.val)))⁻¹ : ℂˣ) : ℂ) •
      σ (adjacentRankLowerLargeProjection (lowerBlockParabolic a.val))
        (adjacentRankLowerTensorCoordinates V z) = _
  simp only [lowerBlockParabolic_largeProjection, adjacentRankDeterminantWeight_apply,
    Langlands.LocalFieldData.determinantComplexPower,
    Langlands.LocalFieldData.determinantUnramifiedCharacter, MonoidHom.comp_apply,
    hd, hb, map_one,
    mul_one, inv_one, Units.val_one, one_smul]

/-- Left multiplication by a unipotent lower diagonal block acts through the
specified original-carrier Whittaker functional. -/
theorem sectionCoefficient_lowerBlock
    (f : (ρ).asModule) (a : upperUnipotent (r + 1) F)
    (g : GeneralLinear (r + 2) F) :
    sectionCoefficient F ψ σ ℓ χ f (lowerBlock a.val * g) =
      (standardCharacter ψ r a : ℂ) * sectionCoefficient F ψ σ ℓ χ f g := by
  unfold sectionCoefficient
  rw [show lowerBlock a.val = (lowerBlockParabolic a.val).val from rfl]
  rw [Induction.eval_covariant, tensorCoordinates_lowerBlock_action]
  exact ℓ.property a _

/-- The literal kernel transforms by the standard ambient character and the
measure-preserving affine column substitution. -/
theorem integrand_unipotent_mul
    (f : (ρ).asModule) (n : upperUnipotent (r + 2) F)
    (g : GeneralLinear (r + 2) F) (x : Fin (r + 1) → F) :
    integrand F ψ σ ℓ χ f (n.val * g) x =
      (standardCharacter ψ (r + 1) n : ℂ) *
        integrand F ψ σ ℓ χ f g (unipotentShift n x) := by
  unfold integrand
  rw [← mul_assoc, upperColumn_mul_unipotent, mul_assoc,
    sectionCoefficient_lowerBlock F ψ σ ℓ χ f ⟨_, unipotentHead_mem n⟩,
    standardCharacter_split, unipotentShift_last]
  have hp : ψ.complex (unipotentColumn n (Fin.last r)) *
      ψ.complex (-(x (Fin.last r) + unipotentColumn n (Fin.last r))) =
        ψ.complex (-x (Fin.last r)) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    abel
  rw [← hp]
  ring

/-- Integration of the exact substitution gives standard Whittaker covariance.
This equality of totalized integrals needs no added convergence premise. -/
theorem integral_unipotent_mul (ν : AdditiveHaarMeasure F)
    (f : (ρ).asModule) (n : upperUnipotent (r + 2) F)
    (g : GeneralLinear (r + 2) F) :
    integral F ψ σ ℓ χ ν f (n.val * g) =
      (standardCharacter ψ (r + 1) n : ℂ) * integral F ψ σ ℓ χ ν f g := by
  unfold integral
  simp_rw [integrand_unipotent_mul]
  rw [integral_const_mul,
    (measurePreserving_unipotentShift F ν n).integral_comp
      (measurableEmbedding_unipotentShift F n)]

/-- Under actual all-section integrability, the scalar Jacquet integral at the
identity is a standard Whittaker functional on the exact host induction. -/
def functional (ν : AdditiveHaarMeasure F)
    (hI : ∀ (f : (ρ).asModule) (g : GeneralLinear (r + 2) F),
      Integrable (integrand F ψ σ ℓ χ f g) (rowMeasure ν (r + 1))) :
    glFunctionals ψ (r + 1) (ρ) :=
  ⟨integralLinear F ψ σ ℓ χ ν hI 1, by
    intro n f
    change integral F ψ σ ℓ χ ν ((ρ) n.val f) 1 =
      (standardCharacter ψ (r + 1) n : ℂ) * integral F ψ σ ℓ χ ν f 1
    rw [integral_right, one_mul]
    simpa only [mul_one] using integral_unipotent_mul F ψ σ ℓ χ ν f n 1⟩

/-- Every coefficient of this single original-carrier functional is the literal
Jacquet integral at that ambient group element. -/
theorem functional_coefficient (ν : AdditiveHaarMeasure F)
    (hI : ∀ (f : (ρ).asModule) (g : GeneralLinear (r + 2) F),
      Integrable (integrand F ψ σ ℓ χ f g) (rowMeasure ν (r + 1)))
    (f : (ρ).asModule) (g : GeneralLinear (r + 2) F) :
    (functional F ψ σ ℓ χ ν hI).val ((ρ) g f) =
      integral F ψ σ ℓ χ ν f g :=
  integralLinear_coefficient F ψ σ ℓ χ ν hI f g

end Padic

end Langlands.AllField.RankinSelberg.AdjacentJacquet
