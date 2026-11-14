import Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergence.RadicalIwasawa
import Langlands.AllField.Group.GL.BlockIwahoriDefinitionsSupplement
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationCell
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationFlat
import Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetConvergence.BoxIntegrability
import Langlands.AllField.Representation.RankinSelberg.UnequalRankMirabolicUnitTestProof
import Langlands.AllField.Representation.Whittaker.MirabolicUnitTestProof
/-!
# Lower Iwasawa factorization of the upper radical

For the upper radical `u(x) = [[1, x], [0, 1]]` of the two-block shape and a lower Iwasawa
factorization `u(x) = q k` with `q` in the lower block parabolic and `k ∈ GL_(t+1)(O)`, the
first diagonal block `A` of `q` has `|det A| = q_F^d` for a natural number `d`, the second
diagonal block has `|det| = q_F^(-d)`, both blocks and their inverses become integral after
multiplication by `ϖ^d`, and so does `x`.
-/

noncomputable section

open scoped NNReal

namespace Langlands.AllField.RankinSelberg.TwoBlockConvergence
open Langlands.RankinSelberg.TwoBlockConvergence hiding box boxFieldLocalField boxFieldTopology boxFieldValuativeRel box_eq_pi exists_radical_factorization measurableSet_box measure_preimage_uniformizer_pow_mul normalizedAbs_determinant_eq_one radicalFieldValuativeRel rectangularMeasure_box
open Langlands.AllField.RankinSelberg.TwoBlockConvergence
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockDeformation hiding blockTensor_twoBlockDeformedBlocks blockZeroNorm blockZeroNorm_mul_integral blockZeroNorm_oppositeParabolic_mul blockZeroNorm_pos compactRadicalJacquet compactRadicalJacquet_inducedRep compactRadicalSubmodule determinantNorm_eq_one_of_mem_upperUnipotent determinantNorm_oppositeLeviProjection_of_mem exists_oppositeParabolic_mul exists_uniform_stabilizer flatFunction flatFunction_covariant flatFunction_mul_flatStabilizer flatSection flatSection_zero flatStabilizer flatStabilizer_le_integralOpen inducedRep_mem_compactRadicalSubmodule integralOpen integral_comp_unipotentShift inverseStandardCharacter_eq_prod inverseTranspose_mem_integralOpen isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule isCompact_integralOpen isLocallyConstant_blockZeroNorm isLocallyConstant_oppositeBlockNorm jacquetFunction_inducedRep_upperUnipotent leviModulus_eq_one mem_compactRadicalSubmodule mem_integralOpen mem_oppositeParabolic_of_lower oppositeBlockNorm oppositeBlockNorm_eq oppositeBlockNorm_mul_integral oppositeBlockNorm_oppositeParabolic_mul oppositeBlockNorm_pos radicalRestriction radicalRestriction_inducedRep sectionEval_leviEmbedding_mul sectionEval_mul_flatStabilizer tensorContraction_blockTensor
open Langlands.AllField.RankinSelberg.TwoBlockDeformation

universe uF uR

section Integral


end Integral

section Determinant



end Determinant

section Padic

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

/-- An element of `GL_(n+1)(O)` has determinant of normalized absolute value one. -/
theorem normalizedAbs_determinant_eq_one {n : ℕ} {k : GeneralLinear (n + 1) F}
    (hk : k ∈ integralOpen F n) :
    (⟨⟩ : LocalFieldData F).normalizedAbs (determinant k : F) = 1 := by
  set T := (⟨⟩ : LocalFieldData F)
  rw [mem_integralOpen] at hk
  have h1 : T.normalizedAbs (determinant k : F) ≤ 1 := by
    rw [T.normalizedAbs_le_one_iff_mem_integers, Matrix.GeneralLinearGroup.val_det_apply]
    exact det_mem_of_forall_mem T.Integers _ hk.1
  have h2 : T.normalizedAbs (determinant k⁻¹ : F) ≤ 1 := by
    rw [T.normalizedAbs_le_one_iff_mem_integers, Matrix.GeneralLinearGroup.val_det_apply]
    exact det_mem_of_forall_mem T.Integers _ hk.2
  have hprod : T.normalizedAbs (determinant k : F) *
      T.normalizedAbs (determinant k⁻¹ : F) = 1 := by
    rw [← T.normalizedAbs_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
      Units.val_one, T.normalizedAbs_one]
  have hnn := T.normalizedAbs_nonneg (determinant k : F)
  have hnn' := T.normalizedAbs_nonneg (determinant k⁻¹ : F)
  nlinarith

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- **Lower Iwasawa factorization of the upper radical.** Every `u(x)` factors as `q k` with
`q` in the lower block parabolic and `k ∈ GL_(t+1)(O)` such that, for one natural number `d`,
`ϖ^d x` is integral, both diagonal blocks of `q` are bounded by `d`, and their determinants
have normalized absolute values `q_F^d` and `q_F^(-d)`. -/
theorem exists_radical_factorization (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) :
    ∃ (q : (succBlockShape m h).oppositeParabolic F)
      (k : GeneralLinear (t + 1) F) (d : ℕ),
      k ∈ integralOpen F t ∧ upperRadical h F x = q * k ∧
        x ∈ box F (m 0 + 1) (m 1 + 1) d ∧
        (∀ i, IsEntryBounded
          (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) d
          ((succBlockShape m h).oppositeLeviProjection F q i)) ∧
        (((⟨⟩ : LocalFieldData F).determinantNorm (m 0 + 1)
            ((succBlockShape m h).oppositeLeviProjection F q 0) : ℝ≥0) : ℝ) =
          ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^ d ∧
        (((⟨⟩ : LocalFieldData F).determinantNorm (m 1 + 1)
            ((succBlockShape m h).oppositeLeviProjection F q 1) : ℝ≥0) : ℝ) =
          (((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^ d)⁻¹ := by
  set T := (⟨⟩ : LocalFieldData F)
  obtain ⟨q, hq, k, hk, hg⟩ :=
    exists_oppositeParabolic_mul F (succBlockShape m h) (upperRadical h F x)
  set Q : (succBlockShape m h).oppositeParabolic F := ⟨q, hq⟩ with hQ
  set A := (succBlockShape m h).oppositeLeviProjection F Q 0 with hA
  set D := (succBlockShape m h).oppositeLeviProjection F Q 1 with hD
  have hk' := (mem_integralOpen F k).1 hk
  have hq1 : (1 : ℝ) < T.residueCardinality := by exact_mod_cast T.residueCardinality_gt_one
  -- the factors in terms of each other
  have hqinv : (q⁻¹ : GeneralLinear (t + 1) F) =
      k * upperRadical h F (-x) := by
    rw [upperRadical_neg, hg, mul_inv_rev, mul_inv_cancel_left]
  have hqval : q = upperRadical h F x * k⁻¹ := by
    rw [hg, mul_inv_cancel_right]
  have hkval : k = q⁻¹ * upperRadical h F x := by
    rw [hg, inv_mul_cancel_left]
  -- entries of the diagonal blocks and of their inverses
  have hAinv' : ∀ a b : Fin (m 0 + 1), ((A⁻¹ : GeneralLinear (m 0 + 1) F) :
        Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F) a b =
      (q⁻¹ : GeneralLinear (t + 1) F) ((succBlockShape m h).index 0 a)
        ((succBlockShape m h).index 0 b) := fun _ _ => rfl
  have hDinv' : ∀ a b : Fin (m 1 + 1), ((D⁻¹ : GeneralLinear (m 1 + 1) F) :
        Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) F) a b =
      (q⁻¹ : GeneralLinear (t + 1) F) ((succBlockShape m h).index 1 a)
        ((succBlockShape m h).index 1 b) := fun _ _ => rfl
  have hD' : ∀ a b : Fin (m 1 + 1),
      (D : Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) F) a b =
        (q : GeneralLinear (t + 1) F) ((succBlockShape m h).index 1 a)
          ((succBlockShape m h).index 1 b) := fun _ _ => rfl
  have hAinv : ∀ a b : Fin (m 0 + 1), ((A⁻¹ : GeneralLinear (m 0 + 1) F) :
        Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F) a b =
      k ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 0 b) := by
    intro a b
    rw [hAinv', hqinv, mul_apply_index h, sum_mul_radical_zero_zero, sum_mul_radical_one_zero,
      add_zero]
  have hDval : ∀ a b : Fin (m 1 + 1),
      (D : Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) F) a b =
        (k⁻¹ : GeneralLinear (t + 1) F) ((succBlockShape m h).index 1 a)
          ((succBlockShape m h).index 1 b) := by
    intro a b
    rw [hD', hqval, mul_apply_index h, sum_radical_one_zero_mul, sum_radical_one_one_mul,
      zero_add]
  have hk01 : ∀ (a : Fin (m 0 + 1)) (b : Fin (m 1 + 1)),
      k ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 b) =
        ∑ c, ((A⁻¹ : GeneralLinear (m 0 + 1) F) :
          Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F) a c * x c b := by
    intro a b
    have hzero : ∀ c : Fin (m 1 + 1), (q⁻¹ : GeneralLinear (t + 1) F)
        ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 c) = 0 :=
      fun c => ((succBlockShape m h).mem_oppositeParabolic_iff F _).1 (inv_mem hq) 0 1
        a c (show (0 : Fin 2) < 1 by decide)
    rw [hkval, mul_apply_index h, sum_mul_radical_zero_one]
    simp only [hzero, zero_mul, Finset.sum_const_zero, add_zero, hAinv']
  -- `x = A k₀₁`
  have hxA : x = (A : Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F) *
      Matrix.of fun c b => k ((succBlockShape m h).index 0 c) ((succBlockShape m h).index 1 b) := by
    have hK : (Matrix.of fun c b =>
          k ((succBlockShape m h).index 0 c) ((succBlockShape m h).index 1 b)) =
        ((A⁻¹ : GeneralLinear (m 0 + 1) F) :
          Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F) * x := by
      ext c b
      rw [Matrix.of_apply, hk01, Matrix.mul_apply]
    rw [hK, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  -- the exponent `d`
  have hAinvInt : ∀ a b : Fin (m 0 + 1), ((A⁻¹ : GeneralLinear (m 0 + 1) F) :
      Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F) a b ∈ T.Integers := by
    intro a b
    rw [hAinv]
    exact hk'.1 _ _
  have hdetAinv : T.normalizedAbs (determinant A⁻¹ : F) ≤ 1 := by
    rw [T.normalizedAbs_le_one_iff_mem_integers, Matrix.GeneralLinearGroup.val_det_apply]
    exact det_mem_of_forall_mem T.Integers _ hAinvInt
  have hprod : T.normalizedAbs (determinant A : F) *
      T.normalizedAbs (determinant A⁻¹ : F) = 1 := by
    rw [← T.normalizedAbs_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
      Units.val_one, T.normalizedAbs_one]
  have hge : 1 ≤ T.normalizedAbs (determinant A : F) := by
    have hnn := T.normalizedAbs_nonneg (determinant A : F)
    nlinarith [mul_nonneg hnn (sub_nonneg.2 hdetAinv)]
  have hord : 0 ≤ -T.ord (determinant A : F) := by
    rw [T.normalizedAbs_of_ne_zero (determinant A).ne_zero] at hge
    exact (one_le_zpow_iff_right₀ hq1).1 hge
  set d := (-T.ord (determinant A : F)).toNat with hd
  have hdz : (d : ℤ) = -T.ord (determinant A : F) := Int.toNat_of_nonneg hord
  have hAnorm : T.normalizedAbs (determinant A : F) =
      (T.residueCardinality : ℝ) ^ d := by
    rw [T.normalizedAbs_of_ne_zero (determinant A).ne_zero, ← hdz, zpow_natCast]
  have hϖnorm : T.normalizedAbs ((T.uniformizer : F) ^ d) =
      ((T.residueCardinality : ℝ) ^ d)⁻¹ := by
    have h' := Langlands.LocalFactor.LocalAbelian.uniformizerUnit_zpow_abs T (d : ℤ)
    rwa [zpow_natCast, Units.val_pow_eq_pow_val, Langlands.LocalFactor.LocalAbelian.uniformizerUnit_coe,
      zpow_neg, zpow_natCast] at h'
  have hϖint : (T.uniformizer : F) ^ d ∈ T.Integers := by
    rw [← T.normalizedAbs_le_one_iff_mem_integers, hϖnorm]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hq1.le)
  have hϖdet : (T.uniformizer : F) ^ d * (determinant A : F) ∈ T.Integers := by
    rw [← T.normalizedAbs_le_one_iff_mem_integers, T.normalizedAbs_mul, hϖnorm, hAnorm,
      inv_mul_cancel₀ (by positivity)]
  have hAbd : ∀ a b : Fin (m 0 + 1), (T.uniformizer : F) ^ d *
      (A : Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F) a b ∈ T.Integers := by
    intro a b
    rw [val_eq_det_smul_adjugate_inv A, Matrix.smul_apply, smul_eq_mul, ← mul_assoc]
    exact mul_mem hϖdet (adjugate_mem_of_forall_mem T.Integers _ hAinvInt a b)
  have hbox : x ∈ box F (m 0 + 1) (m 1 + 1) d := by
    intro a b
    change (T.uniformizer : F) ^ d * x a b ∈ T.Integers
    rw [hxA, Matrix.mul_apply, Finset.mul_sum]
    refine Subring.sum_mem _ fun c _ => ?_
    rw [Matrix.of_apply, ← mul_assoc]
    exact mul_mem (hAbd a c) (hk'.1 _ _)
  -- determinants of the two blocks
  have hkey : T.determinantNorm (m 0 + 1) A * T.determinantNorm (m 1 + 1) D = 1 := by
    have h1 : T.determinantNorm (t + 1) (upperRadical h F x) = 1 := by
      change T.normalizedAbsUnits (determinant (upperRadical h F x)) = 1
      rw [determinant_upperRadical, map_one]
    have h2 : T.determinantNorm (t + 1) k = 1 := by
      apply Units.ext
      apply NNReal.eq
      rw [T.determinantNorm_coe, normalizedAbs_determinant_eq_one F hk]
      rfl
    rw [hg, map_mul, h2, mul_one] at h1
    change T.normalizedAbsUnits (determinant (Q : GeneralLinear (t + 1) F)) = 1 at h1
    rw [determinant_oppositeParabolic, Fin.prod_univ_two, map_mul] at h1
    exact h1
  have hkeyR : ((T.determinantNorm (m 0 + 1) A : ℝ≥0) : ℝ) *
      ((T.determinantNorm (m 1 + 1) D : ℝ≥0) : ℝ) = 1 := by
    rw [← NNReal.coe_mul, ← Units.val_mul, hkey, Units.val_one, NNReal.coe_one]
  have hAnorm' : ((T.determinantNorm (m 0 + 1) A : ℝ≥0) : ℝ) =
      (T.residueCardinality : ℝ) ^ d := by
    rw [T.determinantNorm_coe]
    exact hAnorm
  refine ⟨Q, k, d, hk, hg, hbox, ?_, hAnorm', ?_⟩
  · refine Fin.forall_fin_two.2 ⟨fun a b => ⟨hAbd a b, ?_⟩, fun a b => ⟨?_, ?_⟩⟩
    · change (T.uniformizer : F) ^ d *
        ((A⁻¹ : GeneralLinear (m 0 + 1) F) :
          Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F) a b ∈ T.Integers
      exact mul_mem hϖint (hAinvInt a b)
    · change (T.uniformizer : F) ^ d *
        (D : Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) F) a b ∈ T.Integers
      rw [hDval]
      exact mul_mem hϖint (hk'.2 _ _)
    · change (T.uniformizer : F) ^ d *
        ((D⁻¹ : GeneralLinear (m 1 + 1) F) :
          Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) F) a b ∈ T.Integers
      rw [hDinv', hqinv, mul_apply_index h, sum_mul_radical_zero_one, sum_mul_radical_one_one,
        mul_add, Finset.mul_sum]
      refine add_mem (Subring.sum_mem _ fun c _ => ?_) (mul_mem hϖint (hk'.1 _ _))
      rw [Matrix.neg_apply, mul_neg, mul_neg, mul_left_comm]
      exact neg_mem (mul_mem (hk'.1 _ _) (hbox c b))
  · rw [← hAnorm']
    exact eq_inv_of_mul_eq_one_right hkeyR

end Padic

end Langlands.AllField.RankinSelberg.TwoBlockConvergence
