import Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceDensity
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFixedSliceSupport
/-! # Diagonal density and block-modulus bounds -/

noncomputable section

open scoped BigOperators NNReal

namespace Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice
open Langlands.RankinSelberg.TwoBlockLowerFixedSlice hiding determinantNorm_torus determinantNorm_torus_bounds diagonalDensity diagonalDensity_le exists_coefficient_growth exists_coefficient_rootBounded exists_coefficient_torusSize_growth exists_coefficient_torus_growth exists_section_growth exists_standard_functional_growth instIsNonarchimedeanLocalFieldCarrier instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 isEntryBounded_torus normalizedAbs_uniformizer_zpow torusLevi torusLevi_entryBounded torusLevi_inv_halfModulus_le
open Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement TwoBlockJacquetConvergenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement determinantComplexPower_upperUnipotent isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockDeformation hiding blockTensor_twoBlockDeformedBlocks blockZeroNorm blockZeroNorm_mul_integral blockZeroNorm_oppositeParabolic_mul blockZeroNorm_pos compactRadicalJacquet compactRadicalJacquet_inducedRep compactRadicalSubmodule determinantNorm_eq_one_of_mem_upperUnipotent determinantNorm_oppositeLeviProjection_of_mem exists_oppositeParabolic_mul exists_uniform_stabilizer flatFunction flatFunction_covariant flatFunction_mul_flatStabilizer flatSection flatSection_zero flatStabilizer flatStabilizer_le_integralOpen inducedRep_mem_compactRadicalSubmodule integralOpen integral_comp_unipotentShift inverseStandardCharacter_eq_prod inverseTranspose_mem_integralOpen isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule isCompact_integralOpen isLocallyConstant_blockZeroNorm isLocallyConstant_oppositeBlockNorm jacquetFunction_inducedRep_upperUnipotent leviModulus_eq_one mem_compactRadicalSubmodule mem_integralOpen mem_oppositeParabolic_of_lower oppositeBlockNorm oppositeBlockNorm_eq oppositeBlockNorm_mul_integral oppositeBlockNorm_oppositeParabolic_mul oppositeBlockNorm_pos radicalRestriction radicalRestriction_inducedRep sectionEval_leviEmbedding_mul sectionEval_mul_flatStabilizer tensorContraction_blockTensor
open Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg.TwoBlockConvergence hiding box boxFieldLocalField boxFieldTopology boxFieldValuativeRel box_eq_pi exists_blockTensor_growth exists_bound_isAbsIntegrable_of_factorization exists_functional_growth exists_integral_growth exists_radical_factorization finite_image_sectionEval_integralOpen integrable_integrand_one measurableSet_box measure_preimage_uniformizer_pow_mul norm_integrand_le norm_inv_leviHalfModulus_le_one normalizedAbs_determinant_eq_one proofFieldBorelSpace proofFieldLocalField proofFieldMeasurableSpace proofFieldTopology proofFieldValuativeRel radicalFieldValuativeRel rectangularMeasure_box residue_pow_rpow_neg tensorContraction_blockTensor_twist uniformizerUnit_isUniformizingElement
open Langlands.AllField.RankinSelberg.TwoBlockConvergence

universe uF

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

/-- The inverse upper-Borel modulus appearing in the discrete Iwasawa measure. -/
def diagonalDensity {n : ℕ} (lam : Fin n → ℤ) : ℝ :=
  (∏ i : Fin n, ∏ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
    (⟨⟩ : LocalFieldData F).normalizedAbs
      (((Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F) ^ lam i) /
        (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F) ^ lam j) :
          Fˣ) : F))⁻¹

private theorem prod_le_pow_rank {n : ℕ} (s : Finset (Fin n)) {f : Fin n → ℝ} {R : ℝ}
    (hR : 1 ≤ R) (hf0 : ∀ i ∈ s, 0 ≤ f i) (hf : ∀ i ∈ s, f i ≤ R) :
    ∏ i ∈ s, f i ≤ R ^ n := by
  calc
    _ ≤ ∏ _i ∈ s, R := Finset.prod_le_prod₀ hf0 hf
    _ = R ^ s.card := by simp
    _ ≤ R ^ n := pow_le_pow_right₀ hR (by simpa using Finset.card_le_univ s)

/-- A fixed geometric base bounds every diagonal Iwasawa density. -/
theorem diagonalDensity_le {n : ℕ} (lam : Fin n → ℤ) :
    diagonalDensity F lam ≤
      (((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^ (2 * n * n)) ^
        torusSize lam := by
  set T := (⟨⟩ : LocalFieldData F)
  set q : ℝ := (T.residueCardinality : ℝ)
  have hq : 1 < q := by
    dsimp only [q]
    exact_mod_cast T.residueCardinality_gt_one
  have hR : 1 ≤ q ^ (2 * torusSize lam) := one_le_pow₀ hq.le
  have hroot (i j : Fin n) :
      (T.normalizedAbs
        (((Langlands.LocalFactor.LocalAbelian.uniformizerUnit T ^ lam i) /
          (Langlands.LocalFactor.LocalAbelian.uniformizerUnit T ^ lam j) :
            Fˣ) : F))⁻¹ ≤ q ^ (2 * torusSize lam) := by
    rw [div_eq_mul_inv, ← zpow_sub, normalizedAbs_uniformizer_zpow F,
      ← zpow_neg, neg_neg]
    have he : lam i - lam j ≤ ((2 * torusSize lam : ℕ) : ℤ) := by
      have hi := (torusSize_bounds lam i).2
      have hj := (torusSize_bounds lam j).1
      omega
    simpa only [zpow_natCast] using (zpow_le_zpow_iff_right₀ hq).mpr he
  unfold diagonalDensity
  rw [← Finset.prod_inv_distrib]
  have hprod :
      ∏ i : Fin n, (∏ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
        T.normalizedAbs
          (((Langlands.LocalFactor.LocalAbelian.uniformizerUnit T ^ lam i) /
            (Langlands.LocalFactor.LocalAbelian.uniformizerUnit T ^ lam j) :
              Fˣ) : F))⁻¹ ≤
      ((q ^ (2 * torusSize lam)) ^ n) ^ n := by
    apply prod_le_pow_rank (n := n) Finset.univ (one_le_pow₀ hR (n := n))
    · intro i _
      exact inv_nonneg.mpr
        (Finset.prod_nonneg (fun j _ => T.normalizedAbs_nonneg _))
    · intro i _
      rw [← Finset.prod_inv_distrib]
      exact prod_le_pow_rank _ hR
        (fun j _ => inv_nonneg.mpr (T.normalizedAbs_nonneg _)) (fun j _ => hroot i j)
  calc
    _ ≤ ((q ^ (2 * torusSize lam)) ^ n) ^ n := hprod
    _ = _ := by
      simp only [← pow_mul]
      congr 1
      ring

/-- The determinant of a uniformizer diagonal is exactly the negative
sum of its exponents in normalized absolute value. -/
theorem determinantNorm_torus {n : ℕ} (lam : Fin n → ℤ) :
    (((⟨⟩ : LocalFieldData F).determinantNorm n
      (Iwasawa.torus (Langlands.LocalFactor.LocalAbelian.uniformizerUnit
        (⟨⟩ : LocalFieldData F)) lam) : ℝ≥0) : ℝ) =
      ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^ (-(∑ i, lam i)) := by
  set T := (⟨⟩ : LocalFieldData F)
  have hq : (0 : ℝ) < T.residueCardinality := by
    exact_mod_cast (zero_lt_one.trans T.residueCardinality_gt_one)
  rw [T.determinantNorm_coe]
  change T.normalizedAbs (Iwasawa.torus
    (Langlands.LocalFactor.LocalAbelian.uniformizerUnit T) lam).val.det = _
  rw [Iwasawa.torus_val, Matrix.det_diagonal]
  change (T.normalizedAbsHom
    (∏ i, (((Langlands.LocalFactor.LocalAbelian.uniformizerUnit T) ^ lam i : Fˣ) :
      F)) : ℝ) = _
  rw [map_prod, NNReal.coe_prod]
  simp only [T.normalizedAbsHom_coe]
  dsimp only [T]
  simp only [normalizedAbs_uniformizer_zpow F]
  simp_rw [← Real.rpow_intCast, Int.cast_neg]
  rw [← Real.rpow_sum_of_pos hq]
  congr 1
  simp

/-- Both determinant directions have geometric bounds when each exponent does. -/
theorem determinantNorm_torus_bounds {n e : ℕ} (lam : Fin n → ℤ)
    (he : ∀ i, -(e : ℤ) ≤ lam i ∧ lam i ≤ e) :
    let D : ℝ := (((⟨⟩ : LocalFieldData F).determinantNorm n
      (Iwasawa.torus (Langlands.LocalFactor.LocalAbelian.uniformizerUnit
        (⟨⟩ : LocalFieldData F)) lam) : ℝ≥0) : ℝ)
    D ≤ ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^ (n * e) ∧
      D⁻¹ ≤ ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^ (n * e) := by
  dsimp only
  rw [determinantNorm_torus F, ← zpow_neg, neg_neg]
  have hq : (1 : ℝ) < (⟨⟩ : LocalFieldData F).residueCardinality := by
    exact_mod_cast (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
  have hlo := Finset.sum_le_sum (s := Finset.univ)
    (fun i (_ : i ∈ Finset.univ) => (he i).1)
  have hhi := Finset.sum_le_sum (s := Finset.univ)
    (fun i (_ : i ∈ Finset.univ) => (he i).2)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlo hhi
  constructor
  · have hs : -(∑ i, lam i) ≤ ((n * e : ℕ) : ℤ) := by push_cast; nlinarith
    simpa only [zpow_natCast] using (zpow_le_zpow_iff_right₀ hq).mpr hs
  · have hs : (∑ i, lam i) ≤ ((n * e : ℕ) : ℤ) := by exact_mod_cast hhi
    simpa only [zpow_natCast] using (zpow_le_zpow_iff_right₀ hq).mpr hs

section Blocks

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- Extract the two diagonal blocks of a canonical uniformizer torus. -/
def torusLevi (lam : Fin (t + 1) → ℤ) : (succBlockShape m h).Levi F :=
  fun i => Iwasawa.torus (Langlands.LocalFactor.LocalAbelian.uniformizerUnit
    (⟨⟩ : LocalFieldData F)) (fun a => lam ((succBlockShape m h).index i a))

theorem torusLevi_entryBounded (lam : Fin (t + 1) → ℤ) (i : Fin 2) :
    IsEntryBounded (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F))
      (torusSize lam) (torusLevi F h lam i) :=
  isEntryBounded_torus F (uniformizerUnit_isUniformizingElement F) _
    (torusSize lam) (fun a => torusSize_bounds lam ((succBlockShape m h).index i a))

/-- The actual inverse upper half modulus of these blocks is bounded by a
geometric base independent of the twist and section. -/
theorem torusLevi_inv_halfModulus_le (lam : Fin (t + 1) → ℤ) :
    ‖(((⟨⟩ : LocalFieldData F).leviHalfModulus
      (succBlockShape m h) (torusLevi F h lam) : ℂˣ) : ℂ)⁻¹‖ ≤
      (((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^
        ((m 0 + 1) * (m 1 + 1))) ^ torusSize lam := by
  set T := (⟨⟩ : LocalFieldData F)
  set q : ℝ := (T.residueCardinality : ℝ)
  set b := torusLevi F h lam
  set e := torusSize lam
  have hq : 1 < q := by
    dsimp only [q]
    exact_mod_cast T.residueCardinality_gt_one
  have hd (i : Fin 2) :=
    determinantNorm_torus_bounds F
      (fun a => lam ((succBlockShape m h).index i a))
      (e := e) (fun a => torusSize_bounds lam ((succBlockShape m h).index i a))
  have hlm : ((T.leviModulus (succBlockShape m h) b : ℝ≥0) : ℝ) =
      ((T.determinantNorm (m 0 + 1) (b 0) : ℝ≥0) : ℝ) ^ (m 1 + 1) /
      ((T.determinantNorm (m 1 + 1) (b 1) : ℝ≥0) : ℝ) ^ (m 0 + 1) := by
    rw [T.leviModulus_apply]
    simp only [Finset.prod_filter, Fin.prod_univ_two]
    simp only [Fin.isValue, lt_self_iff_false, ite_false, Fin.zero_lt_one, ite_true,
      not_lt_zero, mul_one, one_mul]
    rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
      NNReal.coe_div, NNReal.coe_pow, NNReal.coe_pow]
  rw [T.leviHalfModulus_apply, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (NNReal.coe_nonneg _), Real.coe_sqrt, ← Real.sqrt_inv]
  apply (Real.sqrt_le_left (pow_nonneg (pow_nonneg (zero_le_one.trans hq.le) _) _)).mpr
  rw [hlm, inv_div, div_eq_mul_inv, ← inv_pow]
  calc
    _ ≤ (q ^ ((m 1 + 1) * e)) ^ (m 0 + 1) *
        (q ^ ((m 0 + 1) * e)) ^ (m 1 + 1) := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ (NNReal.coe_nonneg _) (hd 1).1 _
      · exact pow_le_pow_left₀ (inv_nonneg.mpr (NNReal.coe_nonneg _)) (hd 0).2 _
      · positivity
      · positivity
    _ = _ := by
      simp only [← pow_mul, ← pow_add]
      congr 1
      ring

end Blocks

end Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice
