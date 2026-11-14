import Langlands.Representation.RankinSelberg.AdjacentRankDoubleIntegral
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankCompactMatrixConvergence
noncomputable section

open MeasureTheory Matrix
open scoped BigOperators NNReal ENNReal

namespace Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral
open Langlands.RankinSelberg.AdjacentDoubleIntegral hiding columnHomeomorph columnHomeomorph_apply continuous_integrand doubleIntegralBorel doubleIntegralGLBorel doubleIntegralGLLocallyCompact doubleIntegralGLMeasurable doubleIntegralGLSecondCountable doubleIntegralLocalField doubleIntegralMeasurable doubleIntegralNonarchRing doubleIntegralSecondCountable doubleIntegralSigmaCompact doubleIntegralT2 doubleIntegralTopology doubleIntegralValuativeRel double_integral_eq_modelIntegral double_integral_eq_modelIntegrand double_integral_eq_partialFourier fiberNorm fiberNorm_apply integrable_column integrable_realTwist integral_column_partialFourier integral_mulVec integral_norm_column integrand jacobian_detWeight norm_fiberNorm_apply rowMeasure_map_mulVec
open Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt TwoBlockJacquetConvergenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_rankOneCutoff exists_rankOneEmbedding_support exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rankOneModelValues_subset_whittakerRationalValues rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicMatrixFourierSlice padicRectangularHaarScaling padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mirabolicUnitTest mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open Langlands.RankinSelberg.AdjacentCompactMatrix hiding characterNormExponent characterNormExponent_spec coefficientDeterminantOrder coefficientDeterminantOrder_spec convergenceGLBorel convergenceGLMeasurable convergenceLocalField convergenceMeasurable convergenceNonarchRing convergenceTopology convergenceValuativeRel determinantWeight_add_exponents exists_character_norm_exponent exists_coefficient_det_growth exists_scaled_integral_of_isCompact instIsNonarchimedeanLocalFieldCarrier instTopologicalSpaceCarrier instValuativeRelCarrier integrable_natWeight_of_compact_bound integrable_of_compact_det_growth integrable_realTwist_of_threshold isEntryBounded_of_scaled_integral matrixZeroExtension matrixZeroExtension_apply matrixZeroExtension_of_not_mem_range measurable_matrixZeroExtension norm_realDeterminantWeight norm_realSpectralCharacter norm_realTwistedCharacter pow_ord_mul_abs_pow_le realTwistThreshold realTwistedCharacter transferBorel transferGLBorel transferGLMeasurable transferLocalField transferMeasurable transferSecondCountable transferSigmaCompact transferT2 transferTopology transferValuativeRel uniformizer_pow_ord_div_mem
open Langlands.AllField.RankinSelberg.AdjacentCompactMatrix

universe uF uV
variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance doubleIntegralT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance doubleIntegralNonarchRing : NonarchimedeanRing F := by
  convert! ValuativeRel.nonarchimedeanRing F
  exact Valuation.toTopologicalSpace_eq _
local instance doubleIntegralSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance doubleIntegralSigmaCompact : SigmaCompactSpace F := (⟨⟩ : LocalFieldData F).sigmaCompactSpace
local instance doubleIntegralMeasurable : MeasurableSpace F := borel _
local instance doubleIntegralBorel : BorelSpace F := ⟨rfl⟩
local instance doubleIntegralGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance doubleIntegralGLBorel (n : ℕ) : BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance doubleIntegralGLLocallyCompact (n : ℕ) : LocallyCompactSpace (GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace (n + 1)
local instance doubleIntegralGLSecondCountable (n : ℕ) : SecondCountableTopology (GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology (n + 1)

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

/-- The literal JPSS double-integral scalar kernel, after absorbing a fixed
ambient group element into the rectangular test. -/
def integrand (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (x : Fin (r + 1) → F) (h : GeneralLinear (r + 1) F) : ℂ :=
  Φ (rectangularJoin h.val (h.val *ᵥ x)) * glModelFunction ψ r σ ℓ W h⁻¹ *
    (χ (determinant h) : ℂ) * determinantWeight abv h (((r + 2 : ℕ) : ℂ) / 2) *
      ψ.complex (-x (Fin.last r))

/-- Multiplication by an invertible matrix on column space. -/
def columnHomeomorph {n : ℕ} (h : GeneralLinear n F) :
    (Fin n → F) ≃ₜ (Fin n → F) where
  toFun x := h.val *ᵥ x
  invFun x := (h⁻¹).val *ᵥ x
  left_inv x := by
    dsimp only
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  right_inv x := by
    dsimp only
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

@[simp] theorem columnHomeomorph_apply {n : ℕ} (h : GeneralLinear n F)
    (x : Fin n → F) : columnHomeomorph F h x = h.val *ᵥ x := rfl

/-- The supplied row Haar scales by the reciprocal normalized determinant
under multiplication by the matrix on columns. -/
theorem rowMeasure_map_mulVec (ν : AdditiveHaarMeasure F) {n : ℕ}
    (h : GeneralLinear n F) :
    (rowMeasure ν n).map (fun x => h.val *ᵥ x) =
      ((⟨⟩ : LocalFieldData F).normalizedAbsHom h.val.det)⁻¹ • rowMeasure ν n := by
  exact productMeasure_map_matrix ν.measure (⟨⟩ : LocalFieldData F).normalizedAbsHom
    (fun a ha => padicScalarHaarScaling F (⟨⟩ : LocalFieldData F) ν.measure
      (Units.mk0 a ha)) h.det_ne_zero

/-- Exact Bochner change of variables, retaining the supplied Haar normalization. -/
theorem integral_mulVec (ν : AdditiveHaarMeasure F) {n : ℕ}
    (h : GeneralLinear n F) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : (Fin n → F) → E) :
    (∫ x, f (h.val *ᵥ x) ∂rowMeasure ν n) =
      ((⟨⟩ : LocalFieldData F).normalizedAbs h.val.det)⁻¹ •
        ∫ y, f y ∂rowMeasure ν n := by
  change (∫ x, f (columnHomeomorph F h x) ∂rowMeasure ν n) = _
  rw [← (columnHomeomorph F h).measurableEmbedding.integral_map f]
  change (∫ y, f y ∂(rowMeasure ν n).map (fun x => h.val *ᵥ x)) = _
  rw [rowMeasure_map_mulVec F ν h, integral_smul_nnreal_measure]
  simp only [NNReal.smul_def, NNReal.coe_inv,
    Langlands.LocalFieldData.normalizedAbsHom_coe]

/-- The integral of the absolute value of a last-column slice, as an actual
complex square-matrix Schwartz--Bruhat function. -/
def fiberNorm (ν : AdditiveHaarMeasure F) (r : ℕ)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F)) :
    SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 1)) F) := by
  let f : SchwartzBruhat
      (Matrix (Fin (r + 1)) (Fin (r + 1)) F × (Fin (r + 1) → F)) :=
    Hecke.TestFunction.pullback
    (rectangularSplit (K := F) (n := r + 1)).symm Φ
  exact SchwartzBruhat.partialIntegral (normTest f) (rowMeasure ν (r + 1))

theorem fiberNorm_apply (ν : AdditiveHaarMeasure F) (r : ℕ)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F))
    (A : Matrix (Fin (r + 1)) (Fin (r + 1)) F) :
    fiberNorm F ν r Φ A = (∫ y, ‖Φ (rectangularJoin A y)‖ ∂rowMeasure ν (r + 1) : ℝ) := by
  change (∫ y, (‖Φ (rectangularJoin A y)‖ : ℂ) ∂rowMeasure ν (r + 1)) = _
  exact integral_complex_ofReal

/-- The slice-norm value is a nonnegative real number. -/
theorem norm_fiberNorm_apply (ν : AdditiveHaarMeasure F) (r : ℕ)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F))
    (A : Matrix (Fin (r + 1)) (Fin (r + 1)) F) :
    ‖fiberNorm F ν r Φ A‖ = ∫ y, ‖Φ (rectangularJoin A y)‖ ∂rowMeasure ν (r + 1) := by
  rw [fiberNorm_apply, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]

/-- The column Jacobian reduces the exact half-modulus by one. -/
theorem jacobian_detWeight {r : ℕ} (h : GeneralLinear (r + 1) F) :
    (((⟨⟩ : LocalFieldData F).normalizedAbs h.val.det)⁻¹ : ℂ) *
        determinantWeight abv h (((r + 2 : ℕ) : ℂ) / 2) =
      determinantWeight abv h ((r : ℂ) / 2) := by
  have he : ((r + 2 : ℕ) : ℂ) / 2 = (r : ℂ) / 2 + 1 := by push_cast; ring
  have hw : determinantWeight abv h 1 =
      ((⟨⟩ : LocalFieldData F).normalizedAbs h.val.det : ℂ) := by
    simp only [determinantWeight, Complex.cpow_one, normalizedAbsoluteValue_apply]
  have hd : ((⟨⟩ : LocalFieldData F).normalizedAbs h.val.det : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt ((⟨⟩ : LocalFieldData F).normalizedAbs_pos h.det_ne_zero)
  rw [he, determinantWeight_add_exponents, hw]
  field_simp

/-- Continuity of the literal two-variable kernel requires only smoothness. -/
theorem continuous_integrand (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ)
    (χ : Quasicharacter F)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule) :
    Continuous (fun z : (Fin (r + 1) → F) × GeneralLinear (r + 1) F =>
      integrand F ψ σ ℓ χ Φ W z.1 z.2) := by
  have hc : Continuous (fun z : (Fin (r + 1) → F) × GeneralLinear (r + 1) F =>
      z.2.val) := Units.continuous_val.comp continuous_snd
  exact ((((Φ.continuous.comp (continuous_rectangularJoin.comp
      (hc.prodMk (hc.matrix_mulVec continuous_fst)))).mul
      ((glModelFunction_continuous ψ r σ hσ ℓ W).comp continuous_snd.inv)).mul
      (Units.continuous_val.comp (χ.continuous.comp
        (((⟨⟩ : LocalFieldData F).generalLinearDeterminant (r + 1)).continuous.comp
          continuous_snd)))).mul
      ((continuous_adjacentRank_determinantWeight F _ _).comp continuous_snd)).mul
      (ψ.continuous_complex.comp ((continuous_apply (Fin.last r)).comp continuous_fst).neg)

/-- Every fixed-matrix column section is integrable, without a twist restriction. -/
theorem integrable_column (ν : AdditiveHaarMeasure F)
    (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (h : GeneralLinear (r + 1) F) :
    Integrable (integrand F ψ σ ℓ χ Φ W · h) (rowMeasure ν (r + 1)) := by
  let f := Hecke.TestFunction.pullback (columnHomeomorph F h) (rectangularSlice Φ h.val)
  have hc : Continuous (integrand F ψ σ ℓ χ Φ W · h) :=
    ((((f.continuous.mul continuous_const).mul continuous_const).mul
    continuous_const).mul (ψ.continuous_complex.comp (continuous_apply (Fin.last r)).neg))
  exact hc.integrable_of_hasCompactSupport
    (((f.hasCompactSupport.mul_right).mul_right).mul_right).mul_right

/-- Exact reduction of the integrated column norm to the square-matrix norm. -/
theorem integral_norm_column (ν : AdditiveHaarMeasure F)
    (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (h : GeneralLinear (r + 1) F) :
    (∫ x, ‖integrand F ψ σ ℓ χ Φ W x h‖ ∂rowMeasure ν (r + 1)) =
      ‖fiberNorm F ν r Φ h.val * glModelFunction ψ r σ ℓ W h⁻¹ *
        (χ (determinant h) : ℂ) * determinantWeight abv h ((r : ℂ) / 2)‖ := by
  simp only [integrand, norm_mul, UnitaryAdditiveCharacter.norm_complex, mul_one]
  rw [integral_mul_const, integral_mul_const, integral_mul_const,
    integral_mulVec F ν h (fun y => ‖Φ (rectangularJoin h.val y)‖)]
  rw [norm_fiberNorm_apply]
  have hj := congrArg norm (jacobian_detWeight F h)
  simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ((⟨⟩ : LocalFieldData F).normalizedAbs_nonneg _)] at hj
  simp only [smul_eq_mul]
  rw [← hj]
  ring

/-- Column integration is exactly inverse-character partial Fourier evaluation
at the actual adjacent-rank kernel matrix. -/
theorem integral_column_partialFourier (ν : AdditiveHaarMeasure F)
    (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (h : GeneralLinear (r + 1) F) :
    (∫ x, integrand F ψ σ ℓ χ Φ W x h ∂rowMeasure ν (r + 1)) =
      partialFourierIntegral ψ ν Φ (adjacentRankKernelMatrix h) *
        glModelFunction ψ r σ ℓ W h⁻¹ * (χ (determinant h) : ℂ) *
          determinantWeight abv h ((r : ℂ) / 2) := by
  let f : (Fin (r + 1) → F) → ℂ := fun y =>
    Φ (rectangularJoin h.val y) * ψ.complex (-((h⁻¹).val *ᵥ y) (Fin.last r))
  let C : ℂ := glModelFunction ψ r σ ℓ W h⁻¹ * (χ (determinant h) : ℂ)
  have hf : partialFourierIntegral ψ ν Φ (adjacentRankKernelMatrix h) =
      ∫ y, f y ∂rowMeasure ν (r + 1) := by
    simp only [partialFourierIntegral, rectangularFirstColumns_adjacentRankKernelMatrix,
      rectangularLastColumn_adjacentRankKernelMatrix, rowPairing, f, mulVec, dotProduct]
  have hp : ∀ x, integrand F ψ σ ℓ χ Φ W x h =
      f (h.val *ᵥ x) * C * determinantWeight abv h (((r + 2 : ℕ) : ℂ) / 2) := by
    intro x
    have hx : (h⁻¹).val *ᵥ (h.val *ᵥ x) = x := (columnHomeomorph F h).left_inv x
    dsimp only [integrand, f, C]
    rw [hx]
    ring
  simp_rw [hp]
  rw [integral_mul_const, integral_mul_const, integral_mulVec F ν h f, ← hf,
    Complex.real_smul, Complex.ofReal_inv]
  have hj := jacobian_detWeight F h
  dsimp only [C]
  calc
    _ = partialFourierIntegral ψ ν Φ (adjacentRankKernelMatrix h) *
        glModelFunction ψ r σ ℓ W h⁻¹ * (χ (determinant h) : ℂ) *
        (((⟨⟩ : LocalFieldData F).normalizedAbs h.val.det : ℂ)⁻¹ *
          determinantWeight abv h (((r + 2 : ℕ) : ℂ) / 2)) := by ring
    _ = _ := by rw [hj]

/-- Absolute convergence on the actual product measure above the uniform
square-matrix threshold. -/
theorem integrable_realTwist (ν : AdditiveHaarMeasure F)
    (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (ℓ : glFunctionals ψ r σ)
    (χ₀ : Quasicharacter F) (u : ℝ)
    (hu : realTwistThreshold F ψ σ hσ ℓ χ₀ < u)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F)) :
    Integrable (fun z => integrand F ψ σ ℓ (realTwistedCharacter F χ₀ u) Φ W z.1 z.2)
      ((rowMeasure ν (r + 1)).prod (generalLinearHaar F r)) := by
  apply (integrable_prod_iff'
    (continuous_integrand F ψ σ hσ.1.1 ℓ _ Φ W).aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (integrable_column F ν ψ σ ℓ _ Φ W), ?_⟩
  simpa only [integral_norm_column] using
    (integrable_realTwist_of_threshold F ν ψ σ hσ ℓ χ₀ u hu W (fiberNorm F ν r Φ)).norm

/-- Fubini and the exact column Fourier identity identify the literal JPSS
iterated integral with the partial-Fourier model integral. -/
theorem double_integral_eq_partialFourier (ν : AdditiveHaarMeasure F)
    (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (ℓ : glFunctionals ψ r σ)
    (χ₀ : Quasicharacter F) (u : ℝ)
    (hu : realTwistThreshold F ψ σ hσ ℓ χ₀ < u)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F)) :
    (∫ x, ∫ h, integrand F ψ σ ℓ (realTwistedCharacter F χ₀ u) Φ W x h
      ∂generalLinearHaar F r ∂rowMeasure ν (r + 1)) =
    ∫ h, partialFourierIntegral ψ ν Φ (adjacentRankKernelMatrix h) *
      glModelFunction ψ r σ ℓ W h⁻¹ *
        (realTwistedCharacter F χ₀ u (determinant h) : ℂ) *
          determinantWeight abv h ((r : ℂ) / 2) ∂generalLinearHaar F r := by
  rw [integral_integral_swap (integrable_realTwist F ν ψ σ hσ ℓ χ₀ u hu W Φ)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (integral_column_partialFourier F ν ψ σ ℓ _ Φ W)

/-- At an arbitrary ambient group element, the literal translated double integral
is the integral of the published actual tensor-model integrand. -/
theorem double_integral_eq_modelIntegrand (ν : AdditiveHaarMeasure F)
    (ψ : UnitaryAdditiveCharacter F) (hself : IsSelfDual ψ ν) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (ℓ : glFunctionals ψ r σ)
    (χ₀ : Quasicharacter F) (u : ℝ)
    (hu : realTwistThreshold F ψ σ hσ ℓ χ₀ < u)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F))
    (g : GeneralLinear (r + 2) F) :
    (∫ x, ∫ h, integrand F ψ σ ℓ (realTwistedCharacter F χ₀ u)
      (rectangularTranslate g Φ) W x h
      ∂generalLinearHaar F r ∂rowMeasure ν (r + 1)) =
    ∫ h, adjacentRankModelIntegrand ψ ν hself σ ℓ abv (realTwistedCharacter F χ₀ u)
      ((partialFourierEquiv ψ ν (r + 1) hself Φ) ⊗ₜ[ℂ] W) g h
        ∂generalLinearHaar F r := by
  simpa only [adjacentRankModelIntegrand_tmul, rectangularRho0_intertwine,
    partialFourierEquiv_apply] using
    double_integral_eq_partialFourier F ν ψ σ hσ ℓ χ₀ u hu W (rectangularTranslate g Φ)

/-- Including the exact ambient character and modulus gives the published
adjacent-rank model integral itself. -/
theorem double_integral_eq_modelIntegral (ν : AdditiveHaarMeasure F)
    (ψ : UnitaryAdditiveCharacter F) (hself : IsSelfDual ψ ν) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (ℓ : glFunctionals ψ r σ)
    (χ₀ : Quasicharacter F) (u : ℝ)
    (hu : realTwistThreshold F ψ σ hσ ℓ χ₀ < u)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F))
    (g : GeneralLinear (r + 2) F) :
    (realTwistedCharacter F χ₀ u (determinant g) : ℂ) *
      determinantWeight abv g (((r + 1 : ℕ) : ℂ) / 2) *
      (∫ x, ∫ h, integrand F ψ σ ℓ (realTwistedCharacter F χ₀ u)
        (rectangularTranslate g Φ) W x h
        ∂generalLinearHaar F r ∂rowMeasure ν (r + 1)) =
    adjacentRankModelIntegral ψ ν hself σ ℓ abv (realTwistedCharacter F χ₀ u)
      (generalLinearHaar F r)
      ((partialFourierEquiv ψ ν (r + 1) hself Φ) ⊗ₜ[ℂ] W) g := by
  rw [double_integral_eq_modelIntegrand F ν ψ hself σ hσ ℓ χ₀ u hu W Φ g]
  rfl

end Langlands.AllField.RankinSelberg.AdjacentDoubleIntegral
