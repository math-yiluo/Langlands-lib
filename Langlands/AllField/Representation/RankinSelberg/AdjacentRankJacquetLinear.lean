import Langlands.Representation.RankinSelberg.AdjacentRankJacquetLinear
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankJacquetEvaluation
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory

namespace Langlands.AllField.RankinSelberg.AdjacentJacquet
open Langlands.RankinSelberg.AdjacentJacquet hiding determinantWeight_eq inducedRepresentation integrable_normalizedSection_realTwist integral integralLinear integralLinear_apply integralLinear_coefficient integral_normalizedSection_eq_doubleIntegral integral_normalizedSection_eq_modelIntegral integral_right integrand integrandLinear integrandLinear_apply integrand_normalizedSection integrand_right jacquetEvaluationBorel jacquetEvaluationGLBorel jacquetEvaluationGLLocallyCompact jacquetEvaluationGLMeasurable jacquetEvaluationGLSecondCountable jacquetEvaluationLocalField jacquetEvaluationMeasurable jacquetEvaluationNonarchRing jacquetEvaluationT2 jacquetEvaluationTopology jacquetEvaluationValuativeRel jacquetLinearMeasurable jacquetLinearTopology sectionCoefficient sectionCoefficientLinear sectionCoefficientLinear_apply sectionCoefficient_normalizedSection sectionCoefficient_right
open Langlands.AllField.RankinSelberg.AdjacentJacquet
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneWhittakerTypeStatement SliceIntegrable SliceIntegrableAt TwoBlockJacquetConvergenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement adjacentRankDeterminantWeight adjacentRankDeterminantWeight_apply adjacentRankDeterminantWeight_locallyConstant adjacentRankLowerScalarProjection adjacentRankLower_determinantComplexPower adjacentRankLower_halfModulus adjacentRankLower_weightRatio adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_rankOneCutoff exists_rankOneEmbedding_support exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicMatrixFourierSlice padicRectangularHaarScaling padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic functionalsCongr hasCompactSupport_twoBlockCellRestriction mirabolicUnitTest mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance jacquetLinearMeasurable : MeasurableSpace F := borel _

variable (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
  (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F)

/-- The exact normalized opposite-parabolic representation in the host statement. -/
abbrev inducedRepresentation :=
  (⟨⟩ : LocalFieldData F).normalizedOppositeParabolicInduced (adjacentRankLowerShape r)
    ((adjacentRankLowerShape r).blockTensor
      (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ)))

local notation "ρ" => inducedRepresentation F σ χ

/-- The original-carrier scalar evaluation is linear in the actual induced section. -/
def sectionCoefficientLinear (g : GeneralLinear (r + 2) F) :
    (ρ).asModule →ₗ[ℂ] ℂ where
  toFun f := sectionCoefficient F ψ σ ℓ χ f g
  map_add' f h := by
    change ℓ.val (adjacentRankLowerTensorCoordinates V
      (Induction.eval _ _ f g + Induction.eval _ _ h g)) = _
    rw [map_add, map_add]
    rfl
  map_smul' c f := by
    change ℓ.val (adjacentRankLowerTensorCoordinates V
      (c • Induction.eval _ _ f g)) = _
    rw [map_smul, map_smul]
    rfl

@[simp] theorem sectionCoefficientLinear_apply
    (g : GeneralLinear (r + 2) F) (f : (ρ).asModule) :
    sectionCoefficientLinear F ψ σ ℓ χ g f = sectionCoefficient F ψ σ ℓ χ f g := rfl

/-- Right translation of an actual induced section evaluates by right multiplication. -/
theorem sectionCoefficient_right (k : GeneralLinear (r + 2) F)
    (f : (ρ).asModule) (g : GeneralLinear (r + 2) F) :
    sectionCoefficient F ψ σ ℓ χ (ρ k f) g =
      sectionCoefficient F ψ σ ℓ χ f (g * k) := rfl

/-- The literal Jacquet kernel is linear in the original induced section. -/
def integrandLinear (g : GeneralLinear (r + 2) F) :
    (ρ).asModule →ₗ[ℂ] ((Fin (r + 1) → F) → ℂ) where
  toFun f := integrand F ψ σ ℓ χ f g
  map_add' f h := by
    funext x
    change sectionCoefficientLinear F ψ σ ℓ χ (upperColumn x * g) (f + h) * _ = _
    rw [map_add, add_mul]
    rfl
  map_smul' c f := by
    funext x
    change sectionCoefficientLinear F ψ σ ℓ χ (upperColumn x * g) (c • f) * _ = _
    rw [map_smul, smul_eq_mul, mul_assoc]
    rfl

@[simp] theorem integrandLinear_apply (g : GeneralLinear (r + 2) F)
    (f : (ρ).asModule) : integrandLinear F ψ σ ℓ χ g f = integrand F ψ σ ℓ χ f g := rfl

/-- The Jacquet kernel commutes with the exact right action on the host induction. -/
theorem integrand_right (k : GeneralLinear (r + 2) F)
    (f : (ρ).asModule) (g : GeneralLinear (r + 2) F) :
    integrand F ψ σ ℓ χ (ρ k f) g = integrand F ψ σ ℓ χ f (g * k) := by
  funext x
  unfold integrand
  rw [sectionCoefficient_right, mul_assoc]

/-- The actual scalar Jacquet integral, before imposing its convergence hypothesis. -/
def integral (ν : AdditiveHaarMeasure F) (f : (ρ).asModule)
    (g : GeneralLinear (r + 2) F) : ℂ :=
  ∫ x, integrand F ψ σ ℓ χ f g x ∂rowMeasure ν (r + 1)

/-- Integrating the exact right-translation identity gives coefficient evaluation. -/
theorem integral_right (ν : AdditiveHaarMeasure F)
    (k : GeneralLinear (r + 2) F) (f : (ρ).asModule)
    (g : GeneralLinear (r + 2) F) :
    integral F ψ σ ℓ χ ν (ρ k f) g = integral F ψ σ ℓ χ ν f (g * k) := by
  unfold integral
  rw [integrand_right]

/-- On any family of actual sections with absolute convergence, scalar integration
is a linear map. The hypothesis is discharged by section spanning in the image proof. -/
def integralLinear (ν : AdditiveHaarMeasure F)
    (hI : ∀ (f : (ρ).asModule) (g : GeneralLinear (r + 2) F),
      Integrable (integrand F ψ σ ℓ χ f g) (rowMeasure ν (r + 1)))
    (g : GeneralLinear (r + 2) F) : (ρ).asModule →ₗ[ℂ] ℂ where
  toFun f := integral F ψ σ ℓ χ ν f g
  map_add' f h := by
    change (∫ x, integrandLinear F ψ σ ℓ χ g (f + h) x ∂_) = _
    simp only [map_add, Pi.add_apply]
    exact integral_add (hI f g) (hI h g)
  map_smul' c f := by
    change (∫ x, integrandLinear F ψ σ ℓ χ g (c • f) x ∂_) = _
    simp only [map_smul, Pi.smul_apply]
    exact integral_smul c _

@[simp] theorem integralLinear_apply (ν : AdditiveHaarMeasure F)
    (hI : ∀ (f : (ρ).asModule) (g : GeneralLinear (r + 2) F),
      Integrable (integrand F ψ σ ℓ χ f g) (rowMeasure ν (r + 1)))
    (g : GeneralLinear (r + 2) F) (f : (ρ).asModule) :
    integralLinear F ψ σ ℓ χ ν hI g f = integral F ψ σ ℓ χ ν f g := rfl

/-- The integral at the identity has exactly the scalar Jacquet coefficients at every g. -/
theorem integralLinear_coefficient (ν : AdditiveHaarMeasure F)
    (hI : ∀ (f : (ρ).asModule) (g : GeneralLinear (r + 2) F),
      Integrable (integrand F ψ σ ℓ χ f g) (rowMeasure ν (r + 1)))
    (f : (ρ).asModule) (g : GeneralLinear (r + 2) F) :
    integralLinear F ψ σ ℓ χ ν hI 1 (ρ g f) = integral F ψ σ ℓ χ ν f g := by
  rw [integralLinear_apply, integral_right, one_mul]

end Langlands.AllField.RankinSelberg.AdjacentJacquet
