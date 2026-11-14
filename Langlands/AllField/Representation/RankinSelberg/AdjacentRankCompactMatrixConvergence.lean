import Langlands.Representation.RankinSelberg.AdjacentRankCompactMatrixConvergence
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankCompactMatrixGrowth
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankCompactMatrixIntegrability
noncomputable section

open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace Langlands.AllField.RankinSelberg.AdjacentCompactMatrix
open Langlands.RankinSelberg.AdjacentCompactMatrix hiding characterNormExponent characterNormExponent_spec coefficientDeterminantOrder coefficientDeterminantOrder_spec convergenceGLBorel convergenceGLMeasurable convergenceLocalField convergenceMeasurable convergenceNonarchRing convergenceTopology convergenceValuativeRel determinantWeight_add_exponents exists_character_norm_exponent exists_coefficient_det_growth exists_scaled_integral_of_isCompact instIsNonarchimedeanLocalFieldCarrier instTopologicalSpaceCarrier instValuativeRelCarrier integrable_natWeight_of_compact_bound integrable_of_compact_det_growth integrable_realTwist_of_threshold isEntryBounded_of_scaled_integral matrixZeroExtension matrixZeroExtension_apply matrixZeroExtension_of_not_mem_range measurable_matrixZeroExtension norm_realDeterminantWeight norm_realSpectralCharacter norm_realTwistedCharacter pow_ord_mul_abs_pow_le realTwistThreshold realTwistedCharacter transferBorel transferGLBorel transferGLMeasurable transferLocalField transferMeasurable transferSecondCountable transferSigmaCompact transferT2 transferTopology transferValuativeRel uniformizer_pow_ord_div_mem
open Langlands.AllField.RankinSelberg.AdjacentCompactMatrix
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt TwoBlockJacquetConvergenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice diagonalConj_map disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_rankOneCutoff exists_rankOneEmbedding_support exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rankOneModelValues_subset_whittakerRationalValues rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice singleton_modulus_real sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicMatrixFourierSlice padicRectangularHaarScaling padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mirabolicUnitTest mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear

universe uF uV
variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance convergenceNonarchRing : NonarchimedeanRing F := by
  convert! ValuativeRel.nonarchimedeanRing F
  exact Valuation.toTopologicalSpace_eq _
local instance convergenceMeasurable : MeasurableSpace F := borel _
local instance convergenceGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear (n + 1) F) := borel _
local instance convergenceGLBorel (n : ℕ) : BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

/-- The exact real spectral twist used in the adjacent-rank image statement. -/
def realTwistedCharacter (χ₀ : Quasicharacter F) (u : ℝ) :
    Quasicharacter F :=
  χ₀ * (⟨⟩ : LocalFieldData F).unramifiedCharacterContinuous
    (LocalFactor.spectralParameter (⟨⟩ : LocalFieldData F).residueCardinality
      (⟨⟩ : LocalFieldData F).residueCardinality_real_pos (u : ℂ))

theorem norm_realSpectralCharacter (u : ℝ) (a : Fˣ) :
    ‖((⟨⟩ : LocalFieldData F).unramifiedCharacterContinuous
      (LocalFactor.spectralParameter (⟨⟩ : LocalFieldData F).residueCardinality
        (⟨⟩ : LocalFieldData F).residueCardinality_real_pos (u : ℂ)) a : ℂ)‖ =
      (⟨⟩ : LocalFieldData F).normalizedAbs (a : F) ^ u := by
  change ‖(((LocalFactor.spectralParameter
    ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ)
    (⟨⟩ : LocalFieldData F).residueCardinality_real_pos (u : ℂ)) ^
    (⟨⟩ : LocalFieldData F).ord (a : F) : ℂˣ) : ℂ)‖ = _
  rw [Units.val_zpow_eq_zpow_val]
  rw [norm_zpow, LocalFactor.spectralParameter_eq_cpow,
    Complex.norm_cpow_eq_rpow_re_of_pos (⟨⟩ : LocalFieldData F).residueCardinality_real_pos,
    (⟨⟩ : LocalFieldData F).normalizedAbs_of_ne_zero a.ne_zero,
    ← Real.rpow_intCast, ← Real.rpow_intCast,
    ← Real.rpow_mul (⟨⟩ : LocalFieldData F).residueCardinality_real_pos.le,
    ← Real.rpow_mul (⟨⟩ : LocalFieldData F).residueCardinality_real_pos.le]
  congr 1
  simp only [Complex.neg_re, Complex.ofReal_re, Int.cast_neg]
  ring

theorem exists_character_norm_exponent (χ₀ : Quasicharacter F) :
    ∃ c : ℝ, ∀ a : Fˣ,
      ‖(χ₀ a : ℂ)‖ = (⟨⟩ : LocalFieldData F).normalizedAbs (a : F) ^ c := by
  let : NonarchimedeanGroup (GeneralLinear 1 F) :=
    (⟨⟩ : LocalFieldData F).generalLinearNonarchimedean 1
  have hker : IsOpen ((χ₀.toMonoidHom.comp
      (determinant : GeneralLinear 1 F →* Fˣ)).ker :
        Set (GeneralLinear 1 F)) :=
    isOpen_ker_of_continuous_complex_character _
      (χ₀.continuous.comp ((⟨⟩ : LocalFieldData F).generalLinearDeterminant 1).continuous)
  have hopen : IsOpen (χ₀.toMonoidHom.ker : Set Fˣ) := by
    have h := hker.preimage (scalarContinuous (n := 1) (R := F)).continuous
    change IsOpen {a : Fˣ | χ₀ (determinant (scalar a : GeneralLinear 1 F)) = 1} at h
    change IsOpen {a : Fˣ | χ₀ a = 1}
    simpa only [scalar, determinant, Matrix.GeneralLinearGroup.det_scalar,
      Fintype.card_fin, pow_one] using h
  exact (Langlands.LocalFieldData.smoothCharacterNormDecomposition F
    (⟨⟩ : LocalFieldData F) χ₀.toMonoidHom hopen).exists

/-- The unique real norm exponent of the arbitrary continuous base character. -/
def characterNormExponent (χ₀ : Quasicharacter F) : ℝ :=
  (exists_character_norm_exponent F χ₀).choose

theorem characterNormExponent_spec (χ₀ : Quasicharacter F) (a : Fˣ) :
    ‖(χ₀ a : ℂ)‖ = (⟨⟩ : LocalFieldData F).normalizedAbs (a : F) ^
      characterNormExponent F χ₀ :=
  (exists_character_norm_exponent F χ₀).choose_spec a

theorem norm_realTwistedCharacter (χ₀ : Quasicharacter F) (u : ℝ)
    (a : Fˣ) :
    ‖(realTwistedCharacter F χ₀ u a : ℂ)‖ =
      (⟨⟩ : LocalFieldData F).normalizedAbs (a : F) ^
        (characterNormExponent F χ₀ + u) := by
  change ‖(χ₀ a : ℂ) * ((⟨⟩ : LocalFieldData F).unramifiedCharacterContinuous
    (LocalFactor.spectralParameter (⟨⟩ : LocalFieldData F).residueCardinality
      (⟨⟩ : LocalFieldData F).residueCardinality_real_pos (u : ℂ)) a : ℂ)‖ = _
  rw [norm_mul, characterNormExponent_spec F χ₀ a,
    norm_realSpectralCharacter F u a, ← Real.rpow_add
      ((⟨⟩ : LocalFieldData F).normalizedAbs_pos a.ne_zero)]

/-- The norm of a real determinant weight is its real power. -/
theorem norm_realDeterminantWeight {r : ℕ} (g : GeneralLinear (r + 1) F)
    (s : ℝ) :
    ‖determinantWeight abv g (s : ℂ)‖ =
      (⟨⟩ : LocalFieldData F).normalizedAbs (determinant g : F) ^ s := by
  unfold determinantWeight
  simpa only [Complex.ofReal_re, determinant, Matrix.GeneralLinearGroup.val_det_apply,
    normalizedAbsoluteValue_apply] using
    Complex.norm_cpow_eq_rpow_re_of_pos
      ((normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)).pos g.det_ne_zero) (s : ℂ)

/-- Multiplication of determinant weights at the strictly positive determinant norm. -/
theorem determinantWeight_add_exponents {r : ℕ}
    (g : GeneralLinear (r + 1) F) (s t : ℂ) :
    determinantWeight abv g (s + t) =
      determinantWeight abv g s * determinantWeight abv g t := by
  apply Complex.cpow_add
  exact_mod_cast (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)).ne_zero g.det_ne_zero

/-- Compact square-matrix tests become GL Haar integrable as soon as the
character and determinant powers dominate the coefficient pole and Haar density. -/
theorem integrable_of_compact_det_growth (ν : AdditiveHaarMeasure F)
    (r : ℕ) (f : GeneralLinear (r + 1) F → ℂ) (hf : Continuous f)
    (N : ℕ)
    (hgrowth : ∀ K : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) F),
      IsCompact K → ∃ C : ℝ, 0 ≤ C ∧
        ∀ g : GeneralLinear (r + 1) F, g.val ∈ K →
          ‖f g‖ * (⟨⟩ : LocalFieldData F).normalizedAbs (determinant g : F) ^ N ≤ C)
    (χ : Quasicharacter F) (c : ℝ)
    (hχ : ∀ a : Fˣ,
      ‖(χ a : ℂ)‖ = (⟨⟩ : LocalFieldData F).normalizedAbs (a : F) ^ c)
    (s : ℝ) (hs : (N : ℝ) + (r + 1 : ℕ) ≤ c + s)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 1)) F)) :
    Integrable (fun g : GeneralLinear (r + 1) F =>
      Φ g.val * f g * (χ (determinant g) : ℂ) * determinantWeight abv g (s : ℂ))
        (generalLinearHaar F r) := by
  let K := tsupport (Φ : _ → ℂ)
  have hK : IsCompact K := Φ.hasCompactSupport
  obtain ⟨C, hC, hbound⟩ := hgrowth K hK
  let t : ℝ := s - (r + 1 : ℕ)
  let e : ℝ := c + t - N
  have he : 0 ≤ e := by dsimp [e, t]; linarith
  let A : GeneralLinear (r + 1) F → ℂ := fun g =>
    Φ g.val * f g * (χ (determinant g) : ℂ) * determinantWeight abv g (t : ℂ)
  have hA : Continuous A :=
    (((Φ.continuous.comp Units.continuous_val).mul hf).mul
      (Units.continuous_val.comp (χ.continuous.comp
        ((⟨⟩ : LocalFieldData F).generalLinearDeterminant (r + 1)).continuous))).mul
          (continuous_adjacentRank_determinantWeight F _ _)
  have hAzero : ∀ g : GeneralLinear (r + 1) F, g.val ∉ K → A g = 0 := by
    intro g hg
    simp only [A, image_eq_zero_of_notMem_tsupport hg, zero_mul]
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn Φ.continuous.continuousOn
  have hdetc : Continuous fun X : Matrix (Fin (r + 1)) (Fin (r + 1)) F =>
      (⟨⟩ : LocalFieldData F).normalizedAbs X.det ^ e :=
    (Real.continuous_rpow_const he).comp
      ((⟨⟩ : LocalFieldData F).continuous_normalizedAbs.comp continuous_id.matrix_det)
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn hdetc.continuousOn
  have hAnorm (g : GeneralLinear (r + 1) F) :
      ‖A g‖ = ‖Φ g.val‖ *
        (‖f g‖ * (⟨⟩ : LocalFieldData F).normalizedAbs (determinant g : F) ^ N) *
          (⟨⟩ : LocalFieldData F).normalizedAbs (determinant g : F) ^ e := by
    let d := (⟨⟩ : LocalFieldData F).normalizedAbs (determinant g : F)
    have hd : 0 < d := (⟨⟩ : LocalFieldData F).normalizedAbs_pos (determinant g).ne_zero
    have hexp : c + t = (N : ℝ) + e := by dsimp [e]; ring
    simp only [A, norm_mul, hχ, norm_realDeterminantWeight]
    change ‖Φ g.val‖ * ‖f g‖ * d ^ c * d ^ t =
      ‖Φ g.val‖ * (‖f g‖ * d ^ N) * d ^ e
    calc
      _ = ‖Φ g.val‖ * ‖f g‖ * (d ^ c * d ^ t) := by ring
      _ = ‖Φ g.val‖ * ‖f g‖ * d ^ ((N : ℝ) + e) := by
        rw [← Real.rpow_add hd, hexp]
      _ = _ := by rw [Real.rpow_add hd, Real.rpow_natCast]; ring
  have hAbound (g : GeneralLinear (r + 1) F) (hg : g.val ∈ K) :
      ‖A g‖ ≤ max B 0 * C * max D 0 := by
    rw [hAnorm]
    have hb : ‖Φ g.val‖ ≤ max B 0 := (hB g.val hg).trans (le_max_left _ _)
    have hd : (⟨⟩ : LocalFieldData F).normalizedAbs (determinant g : F) ^ e ≤
        max D 0 := by
      apply le_trans _ (le_max_left _ _)
      have h := hD g.val hg
      exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, determinant,
        Matrix.GeneralLinearGroup.val_det_apply] using h)
    exact mul_le_mul
      (mul_le_mul hb (hbound g hg)
        (mul_nonneg (norm_nonneg _) (pow_nonneg
          ((⟨⟩ : LocalFieldData F).normalizedAbs_nonneg _) _))
        (le_max_right _ _)) hd
      (Real.rpow_nonneg ((⟨⟩ : LocalFieldData F).normalizedAbs_nonneg _) _)
      (mul_nonneg (le_max_right _ _) hC)
  have hi := integrable_natWeight_of_compact_bound F ν r A hA K hK hAzero
    (max B 0 * C * max D 0)
    (mul_nonneg (mul_nonneg (le_max_right _ _) hC) (le_max_right _ _)) hAbound
  convert hi using 1
  funext g
  have hs' : (s : ℂ) = (r + 1 : ℕ) + (t : ℂ) := by dsimp [t]; push_cast; ring
  rw [hs', determinantWeight_add_exponents]
  dsimp [A]
  ring

/-- A single sufficient real-twist threshold chosen before coefficient vectors
and square-matrix tests. No optimality is asserted. -/
def realTwistThreshold (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (ℓ : glFunctionals ψ r σ)
    (χ₀ : Quasicharacter F) : ℝ :=
  (coefficientDeterminantOrder F ψ σ hσ ℓ : ℝ) -
    characterNormExponent F χ₀ + (r + 1 : ℕ) - (r : ℝ) / 2

/-- The exact real spectral twists give genuine GL Haar integrability for
every coefficient vector and every square-matrix Schwartz--Bruhat test above
one uniform threshold. -/
theorem integrable_realTwist_of_threshold
    (ν : AdditiveHaarMeasure F)
    (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (ℓ : glFunctionals ψ r σ)
    (χ₀ : Quasicharacter F) (u : ℝ)
    (hu : realTwistThreshold F ψ σ hσ ℓ χ₀ < u)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 1)) F)) :
    Integrable (fun g : GeneralLinear (r + 1) F =>
      Φ g.val * glModelFunction ψ r σ ℓ W g⁻¹ *
        (realTwistedCharacter F χ₀ u (determinant g) : ℂ) *
          determinantWeight abv g ((r : ℂ) / 2))
      (generalLinearHaar F r) := by
  have hs : (coefficientDeterminantOrder F ψ σ hσ ℓ : ℝ) +
      (r + 1 : ℕ) ≤ (characterNormExponent F χ₀ + u) + (r : ℝ) / 2 := by
    dsimp [realTwistThreshold] at hu
    linarith
  simpa only [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat] using
    integrable_of_compact_det_growth F ν r
      (fun g => glModelFunction ψ r σ ℓ W g⁻¹)
      ((glModelFunction_continuous ψ r σ hσ.1.1 ℓ W).comp continuous_inv)
      (coefficientDeterminantOrder F ψ σ hσ ℓ)
      (coefficientDeterminantOrder_spec F ψ σ hσ ℓ W)
      (realTwistedCharacter F χ₀ u) (characterNormExponent F χ₀ + u)
      (norm_realTwistedCharacter F χ₀ u) ((r : ℝ) / 2) hs Φ

end Langlands.AllField.RankinSelberg.AdjacentCompactMatrix
