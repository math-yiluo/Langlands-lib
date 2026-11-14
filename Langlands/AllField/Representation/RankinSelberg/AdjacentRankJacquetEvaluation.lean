import Langlands.Representation.RankinSelberg.AdjacentRankJacquetEvaluation
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankDoubleIntegral
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankNormalizedSection
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Matrix
open scoped TensorProduct

namespace Langlands.AllField.RankinSelberg.AdjacentJacquet
open Langlands.RankinSelberg.AdjacentJacquet hiding determinantWeight_eq integrable_normalizedSection_realTwist integral_normalizedSection_eq_doubleIntegral integral_normalizedSection_eq_modelIntegral integrand integrand_normalizedSection jacquetEvaluationBorel jacquetEvaluationGLBorel jacquetEvaluationGLLocallyCompact jacquetEvaluationGLMeasurable jacquetEvaluationGLSecondCountable jacquetEvaluationLocalField jacquetEvaluationMeasurable jacquetEvaluationNonarchRing jacquetEvaluationT2 jacquetEvaluationTopology jacquetEvaluationValuativeRel sectionCoefficient sectionCoefficient_normalizedSection
open Langlands.AllField.RankinSelberg.AdjacentJacquet
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneWhittakerTypeStatement SliceIntegrable SliceIntegrableAt TwoBlockJacquetConvergenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement adjacentRankDeterminantWeight adjacentRankDeterminantWeight_apply adjacentRankDeterminantWeight_locallyConstant adjacentRankLowerScalarProjection adjacentRankLower_determinantComplexPower adjacentRankLower_halfModulus adjacentRankLower_weightRatio adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_rankOneCutoff exists_rankOneEmbedding_support exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicMatrixFourierSlice padicRectangularHaarScaling padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic functionalsCongr hasCompactSupport_twoBlockCellRestriction mirabolicUnitTest mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open Langlands.RankinSelberg.AdjacentCompactMatrix hiding characterNormExponent characterNormExponent_spec coefficientDeterminantOrder coefficientDeterminantOrder_spec convergenceGLBorel convergenceGLMeasurable convergenceLocalField convergenceMeasurable convergenceNonarchRing convergenceTopology convergenceValuativeRel determinantWeight_add_exponents exists_character_norm_exponent exists_coefficient_det_growth exists_scaled_integral_of_isCompact instIsNonarchimedeanLocalFieldCarrier instTopologicalSpaceCarrier instValuativeRelCarrier integrable_natWeight_of_compact_bound integrable_of_compact_det_growth integrable_realTwist_of_threshold isEntryBounded_of_scaled_integral matrixZeroExtension matrixZeroExtension_apply matrixZeroExtension_of_not_mem_range measurable_matrixZeroExtension norm_realDeterminantWeight norm_realSpectralCharacter norm_realTwistedCharacter pow_ord_mul_abs_pow_le realTwistThreshold realTwistedCharacter transferBorel transferGLBorel transferGLMeasurable transferLocalField transferMeasurable transferSecondCountable transferSigmaCompact transferT2 transferTopology transferValuativeRel uniformizer_pow_ord_div_mem
open Langlands.AllField.RankinSelberg.AdjacentCompactMatrix

universe uF uV

section Column


end Column

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance jacquetEvaluationT2 : T2Space F :=
  (⟨⟩ : LocalFieldData F).fieldT2
local instance jacquetEvaluationNonarchRing : NonarchimedeanRing F := by
  convert! ValuativeRel.nonarchimedeanRing F
  exact Valuation.toTopologicalSpace_eq _
local instance jacquetEvaluationMeasurable : MeasurableSpace F := borel _
local instance jacquetEvaluationBorel : BorelSpace F := ⟨rfl⟩
local instance jacquetEvaluationGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance jacquetEvaluationGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance jacquetEvaluationGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace (n + 1)
local instance jacquetEvaluationGLSecondCountable (n : ℕ) :
    SecondCountableTopology (GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology (n + 1)

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

/-- The smooth determinant character agrees with the exact scalar integral weight. -/
theorem determinantWeight_eq (χ : Quasicharacter F) (n : ℕ)
    (s : ℂ) (g : GeneralLinear n F) :
    ((adjacentRankDeterminantWeight (⟨⟩ : LocalFieldData F) χ n s).toMonoidHom g : ℂ) =
      (χ (determinant g) : ℂ) * determinantWeight abv g s := by
  rw [adjacentRankDeterminantWeight_apply, Units.val_mul,
    (⟨⟩ : LocalFieldData F).determinantComplexPower_apply]
  rfl

variable (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
  (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F)

/-- Scalar evaluation of an actual normalized section through the original module. -/
def sectionCoefficient
    (f : ((⟨⟩ : LocalFieldData F).normalizedOppositeParabolicInduced (adjacentRankLowerShape r)
      ((adjacentRankLowerShape r).blockTensor
        (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ)))).asModule)
    (g : GeneralLinear (r + 2) F) : ℂ :=
  ℓ.val (adjacentRankLowerTensorCoordinates V
    (Induction.eval ((adjacentRankLowerShape r).oppositeParabolic F)
      (Langlands.AllField.RankinSelberg.Padic.adjacentRankLowerTensorRepresentation F σ χ) f g))

/-- The literal scalar Jacquet kernel, with the inverse last-coordinate phase. -/
def integrand
    (f : ((⟨⟩ : LocalFieldData F).normalizedOppositeParabolicInduced (adjacentRankLowerShape r)
      ((adjacentRankLowerShape r).blockTensor
        (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ)))).asModule)
    (g : GeneralLinear (r + 2) F) (x : Fin (r + 1) → F) : ℂ :=
  sectionCoefficient F ψ σ ℓ χ f (upperColumn x * g) *
    ψ.complex (-x (Fin.last r))

/-- Pure normalized sections retain their original-carrier algebraic average
after scalar evaluation. -/
theorem sectionCoefficient_normalizedSection (hσ : IsSmooth σ)
    (Φ : adjacentRankCompactTests (r + 1) F) (v : V)
    (g : GeneralLinear (r + 2) F) :
    sectionCoefficient F ψ σ ℓ χ (Langlands.AllField.RankinSelberg.Padic.adjacentRankNormalizedSection F σ χ hσ Φ v) g =
      ((adjacentRankDeterminantWeight (⟨⟩ : LocalFieldData F) χ
        (r + 2) (((r + 1 : ℕ) : ℂ) / 2)).toMonoidHom g : ℂ) *
      (∫ h, Φ.val (rectangularJoin h.val 0 * g.val) *
        ((adjacentRankDeterminantWeight (⟨⟩ : LocalFieldData F) χ
          (r + 1) (((r + 2 : ℕ) : ℂ) / 2)).toMonoidHom h : ℂ) *
        ℓ.val (σ h⁻¹ v) ∂generalLinearHaar F r) := by
  unfold sectionCoefficient
  rw [Langlands.AllField.RankinSelberg.Padic.adjacentRankNormalizedSection_eval,
    adjacentRankLowerTensorCoordinates_pairTensor, one_smul, map_smul,
    smul_eq_mul, adjacentRankCompactAverage_dual]

/-- The actual pure-section Jacquet kernel is the translated literal inner
integral, with precisely the ambient normalized determinant weight. -/
theorem integrand_normalizedSection (hσ : IsSmooth σ)
    (Φ : adjacentRankCompactTests (r + 1) F) (v : V)
    (g : GeneralLinear (r + 2) F) (x : Fin (r + 1) → F) :
    integrand F ψ σ ℓ χ (Langlands.AllField.RankinSelberg.Padic.adjacentRankNormalizedSection F σ χ hσ Φ v) g x =
      ((adjacentRankDeterminantWeight (⟨⟩ : LocalFieldData F) χ
        (r + 2) (((r + 1 : ℕ) : ℂ) / 2)).toMonoidHom g : ℂ) *
      ∫ h, Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral.integrand F ψ σ ℓ χ
        (rectangularTranslate g Φ) (modelMap σ ℓ v) x h
          ∂generalLinearHaar F r := by
  have hweight :
      ((adjacentRankDeterminantWeight (⟨⟩ : LocalFieldData F) χ
        (r + 2) (((r + 1 : ℕ) : ℂ) / 2)).toMonoidHom (upperColumn x * g) : ℂ) =
      ((adjacentRankDeterminantWeight (⟨⟩ : LocalFieldData F) χ
        (r + 2) (((r + 1 : ℕ) : ℂ) / 2)).toMonoidHom g : ℂ) := by
    rw [map_mul, Units.val_mul]
    have hc :
        (adjacentRankDeterminantWeight (⟨⟩ : LocalFieldData F) χ
          (r + 2) (((r + 1 : ℕ) : ℂ) / 2)).toMonoidHom (upperColumn x) = 1 := by
      simp [adjacentRankDeterminantWeight_apply,
        Langlands.LocalFieldData.determinantComplexPower,
        (⟨⟩ : LocalFieldData F).ord_one]
    rw [hc, Units.val_one, one_mul]
  unfold integrand
  rw [sectionCoefficient_normalizedSection, hweight, mul_assoc, ← integral_mul_const]
  apply congrArg (_ * ·)
  apply integral_congr_ae
  filter_upwards with h
  simp only [Units.val_mul, ← Matrix.mul_assoc, rectangularJoin_mul_upperColumn,
    determinantWeight_eq, Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral.integrand, rectangularTranslate_apply]
  change Φ.val (rectangularJoin h.val (h.val *ᵥ x) * g.val) *
      ((χ (determinant h) : ℂ) *
        determinantWeight abv h (((r + 2 : ℕ) : ℂ) / 2)) *
      ℓ.val (σ h⁻¹ v) * ψ.complex (-x (Fin.last r)) =
    Φ.val (rectangularJoin h.val (h.val *ᵥ x) * g.val) *
      ℓ.val (σ h⁻¹ v) * (χ (determinant h) : ℂ) *
      determinantWeight abv h (((r + 2 : ℕ) : ℂ) / 2) *
      ψ.complex (-x (Fin.last r))
  ring

/-- Actual scalar Jacquet integrability of every pure normalized compact section
uses the same representation-uniform threshold as the double integral. -/
theorem integrable_normalizedSection_realTwist (ν : AdditiveHaarMeasure F)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
    (χ₀ : Quasicharacter F) (u : ℝ)
    (hu : realTwistThreshold F ψ σ hσ ℓ χ₀ < u)
    (Φ : adjacentRankCompactTests (r + 1) F) (v : V)
    (g : GeneralLinear (r + 2) F) :
    Integrable
      (integrand F ψ σ ℓ (realTwistedCharacter F χ₀ u)
        (Langlands.AllField.RankinSelberg.Padic.adjacentRankNormalizedSection F σ
          (realTwistedCharacter F χ₀ u) hσ.1.1 Φ v) g)
      (rowMeasure ν (r + 1)) := by
  apply Integrable.congr
    ((Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral.integrable_realTwist F ν ψ σ hσ ℓ χ₀ u hu
      (modelMap σ ℓ v) (rectangularTranslate g Φ)).integral_prod_left.const_mul
        ((adjacentRankDeterminantWeight (⟨⟩ : LocalFieldData F)
          (realTwistedCharacter F χ₀ u) (r + 2)
            (((r + 1 : ℕ) : ℂ) / 2)).toMonoidHom g : ℂ))
  exact Filter.Eventually.of_forall fun x =>
    (integrand_normalizedSection F ψ σ ℓ _ hσ.1.1 Φ v g x).symm

/-- Scalar integration of a pure normalized section retains the literal
iterated double integral, including its exact outer determinant weight. -/
theorem integral_normalizedSection_eq_doubleIntegral (ν : AdditiveHaarMeasure F)
    (hσ : IsSmooth σ)
    (Φ : adjacentRankCompactTests (r + 1) F) (v : V)
    (g : GeneralLinear (r + 2) F) :
    (∫ x, integrand F ψ σ ℓ χ
      (Langlands.AllField.RankinSelberg.Padic.adjacentRankNormalizedSection F σ χ hσ Φ v) g x
        ∂rowMeasure ν (r + 1)) =
    ((adjacentRankDeterminantWeight (⟨⟩ : LocalFieldData F) χ
      (r + 2) (((r + 1 : ℕ) : ℂ) / 2)).toMonoidHom g : ℂ) *
      ∫ x, ∫ h, Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral.integrand F ψ σ ℓ χ
        (rectangularTranslate g Φ) (modelMap σ ℓ v) x h
          ∂generalLinearHaar F r ∂rowMeasure ν (r + 1) := by
  simp_rw [integrand_normalizedSection]
  rw [integral_const_mul]

/-- The actual Jacquet integral on each pure original-carrier normalized section
is precisely the published pure-tensor model integral, as a function of every g. -/
theorem integral_normalizedSection_eq_modelIntegral (ν : AdditiveHaarMeasure F)
    (hself : IsSelfDual ψ ν)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
    (χ₀ : Quasicharacter F) (u : ℝ)
    (hu : realTwistThreshold F ψ σ hσ ℓ χ₀ < u)
    (Φ : adjacentRankCompactTests (r + 1) F) (v : V)
    (g : GeneralLinear (r + 2) F) :
    (∫ x, integrand F ψ σ ℓ (realTwistedCharacter F χ₀ u)
      (Langlands.AllField.RankinSelberg.Padic.adjacentRankNormalizedSection F σ (realTwistedCharacter F χ₀ u)
        hσ.1.1 Φ v) g x ∂rowMeasure ν (r + 1)) =
    adjacentRankModelIntegral ψ ν hself σ ℓ abv (realTwistedCharacter F χ₀ u)
      (generalLinearHaar F r)
      ((partialFourierEquiv ψ ν (r + 1) hself Φ.val) ⊗ₜ[ℂ] (modelMap σ ℓ v)) g := by
  rw [integral_normalizedSection_eq_doubleIntegral, determinantWeight_eq]
  exact Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral.double_integral_eq_modelIntegral
    F ν ψ hself σ hσ ℓ χ₀ u hu (modelMap σ ℓ v) Φ.val g

end Langlands.AllField.RankinSelberg.AdjacentJacquet
