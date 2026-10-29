import Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergence.FunctionalGrowth
import Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergence.BoxIntegrability
import Langlands.Representation.RankinSelberg.TwoBlockDeformationFlat
import Langlands.Representation.RankinSelberg.TwoBlockDeformationCell

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

namespace Langlands.RankinSelberg.TwoBlockConvergence

open GeneralLinear TwoBlockJacquet TwoBlockDeformation

universe uF uR

section Integral

variable {R : Type uR} [CommRing R] (S : Subring R)

/-- The determinant of a matrix with entries in a subring lies in the subring. -/
theorem det_mem_of_forall_mem {r : ℕ} (M : Matrix (Fin r) (Fin r) R) (hM : ∀ a b, M a b ∈ S) :
    M.det ∈ S := by
  let M' : Matrix (Fin r) (Fin r) S := Matrix.of fun a b => ⟨M a b, hM a b⟩
  have hM' : S.subtype.mapMatrix M' = M := by
    ext a b
    rfl
  rw [← hM', ← RingHom.map_det]
  exact M'.det.property

/-- The adjugate of a matrix with entries in a subring has entries in the subring. -/
theorem adjugate_mem_of_forall_mem {r : ℕ} (M : Matrix (Fin r) (Fin r) R)
    (hM : ∀ a b, M a b ∈ S) (a b : Fin r) : M.adjugate a b ∈ S := by
  let M' : Matrix (Fin r) (Fin r) S := Matrix.of fun a b => ⟨M a b, hM a b⟩
  have hM' : S.subtype.mapMatrix M' = M := by
    ext a b
    rfl
  rw [← hM', ← RingHom.map_adjugate]
  exact (M'.adjugate a b).property

/-- An invertible matrix is its determinant times the adjugate of its inverse. -/
theorem val_eq_det_smul_adjugate_inv {r : ℕ} (A : GeneralLinear r R) :
    (A : Matrix (Fin r) (Fin r) R) =
      (determinant A : R) • ((A⁻¹ : GeneralLinear r R) : Matrix (Fin r) (Fin r) R).adjugate := by
  have h1 : ((A⁻¹ : GeneralLinear r R) : Matrix (Fin r) (Fin r) R) *
      ((determinant A : R) • ((A⁻¹ : GeneralLinear r R) : Matrix (Fin r) (Fin r) R).adjugate) =
        1 := by
    rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, Matrix.GeneralLinearGroup.val_det_apply,
      ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, one_smul]
  calc
    (A : Matrix (Fin r) (Fin r) R) =
        (A : Matrix (Fin r) (Fin r) R) * (((A⁻¹ : GeneralLinear r R) : Matrix (Fin r) (Fin r) R) *
          ((determinant A : R) •
            ((A⁻¹ : GeneralLinear r R) : Matrix (Fin r) (Fin r) R).adjugate)) := by
      rw [h1, Matrix.mul_one]
    _ = _ := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]

end Integral

section Determinant

variable {R : Type uR} [CommRing R]

/-- The determinant of an element of a lower block parabolic is the product of the
determinants of its diagonal blocks. -/
theorem determinant_oppositeParabolic {n : ℕ} (B : BlockShape n) (q : B.oppositeParabolic R) :
    determinant (q : GeneralLinear n R) = ∏ i, determinant (B.oppositeLeviProjection R q i) := by
  classical
  apply Units.ext
  have hq : ((reindex (R := R) B.indexEquiv).symm (q : GeneralLinear n R)).val.BlockTriangular
      (fun a : B.Index => OrderDual.toDual a.1) := q.property
  rw [Matrix.GeneralLinearGroup.val_det_apply,
    ← Matrix.det_reindex_self B.indexEquiv.symm (q : GeneralLinear n R).val]
  change ((reindex (R := R) B.indexEquiv).symm (q : GeneralLinear n R)).val.det = _
  rw [hq.det_fintype, Units.coe_prod]
  refine Fintype.prod_equiv OrderDual.ofDual _ _ fun i => ?_
  let e : Fin (B.size (OrderDual.ofDual i)) ≃
      {a : B.Index // OrderDual.toDual a.1 = i} :=
    Equiv.ofBijective (fun j => ⟨⟨OrderDual.ofDual i, j⟩, rfl⟩) (by
      constructor
      · intro j k hjk
        exact eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Subtype.val hjk)).2
      · rintro ⟨⟨k, j⟩, hk⟩
        subst hk
        exact ⟨j, rfl⟩)
  rw [← Matrix.det_submatrix_equiv_self e]
  rfl

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- The upper radical has determinant one. -/
theorem determinant_upperRadical (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R) :
    determinant (upperRadical h R x) = 1 := by
  apply Units.ext
  change Matrix.det (Matrix.reindex (finCongr (blockRanks_add h)) (finCongr (blockRanks_add h))
    (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 x 0 1))) = 1
  rw [Matrix.det_reindex_self, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, Matrix.det_one, mul_one]

end Determinant

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance radicalFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance radicalFieldValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance radicalFieldLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

/-- An element of `GL_(n+1)(O)` has determinant of normalized absolute value one. -/
theorem normalizedAbs_determinant_eq_one {n : ℕ} {k : GeneralLinear (n + 1) F.Carrier}
    (hk : k ∈ integralOpen F n) :
    F.canonicalTopologicalData.normalizedAbs (determinant k : F.Carrier) = 1 := by
  set T := F.canonicalTopologicalData
  rw [mem_integralOpen] at hk
  have h1 : T.normalizedAbs (determinant k : F.Carrier) ≤ 1 := by
    rw [T.normalizedAbs_le_one_iff_mem_integers, Matrix.GeneralLinearGroup.val_det_apply]
    exact det_mem_of_forall_mem T.Integers _ hk.1
  have h2 : T.normalizedAbs (determinant k⁻¹ : F.Carrier) ≤ 1 := by
    rw [T.normalizedAbs_le_one_iff_mem_integers, Matrix.GeneralLinearGroup.val_det_apply]
    exact det_mem_of_forall_mem T.Integers _ hk.2
  have hprod : T.normalizedAbs (determinant k : F.Carrier) *
      T.normalizedAbs (determinant k⁻¹ : F.Carrier) = 1 := by
    rw [← T.normalizedAbs_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
      Units.val_one, T.normalizedAbs_one]
  have hnn := T.normalizedAbs_nonneg (determinant k : F.Carrier)
  have hnn' := T.normalizedAbs_nonneg (determinant k⁻¹ : F.Carrier)
  nlinarith

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- **Lower Iwasawa factorization of the upper radical.** Every `u(x)` factors as `q k` with
`q` in the lower block parabolic and `k ∈ GL_(t+1)(O)` such that, for one natural number `d`,
`ϖ^d x` is integral, both diagonal blocks of `q` are bounded by `d`, and their determinants
have normalized absolute values `q_F^d` and `q_F^(-d)`. -/
theorem exists_radical_factorization (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) :
    ∃ (q : (succBlockShape m h).oppositeParabolic F.Carrier)
      (k : GeneralLinear (t + 1) F.Carrier) (d : ℕ),
      k ∈ integralOpen F t ∧ upperRadical h F.Carrier x = q * k ∧
        x ∈ box F (m 0 + 1) (m 1 + 1) d ∧
        (∀ i, IsEntryBounded
          (LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData) d
          ((succBlockShape m h).oppositeLeviProjection F.Carrier q i)) ∧
        ((F.canonicalTopologicalData.determinantNorm (m 0 + 1)
            ((succBlockShape m h).oppositeLeviProjection F.Carrier q 0) : ℝ≥0) : ℝ) =
          (F.canonicalTopologicalData.residueCardinality : ℝ) ^ d ∧
        ((F.canonicalTopologicalData.determinantNorm (m 1 + 1)
            ((succBlockShape m h).oppositeLeviProjection F.Carrier q 1) : ℝ≥0) : ℝ) =
          ((F.canonicalTopologicalData.residueCardinality : ℝ) ^ d)⁻¹ := by
  set T := F.canonicalTopologicalData
  obtain ⟨q, hq, k, hk, hg⟩ :=
    exists_oppositeParabolic_mul F (succBlockShape m h) (upperRadical h F.Carrier x)
  set Q : (succBlockShape m h).oppositeParabolic F.Carrier := ⟨q, hq⟩ with hQ
  set A := (succBlockShape m h).oppositeLeviProjection F.Carrier Q 0 with hA
  set D := (succBlockShape m h).oppositeLeviProjection F.Carrier Q 1 with hD
  have hk' := (mem_integralOpen F k).1 hk
  have hq1 : (1 : ℝ) < T.residueCardinality := by exact_mod_cast T.residueCardinality_gt_one
  -- the factors in terms of each other
  have hqinv : (q⁻¹ : GeneralLinear (t + 1) F.Carrier) =
      k * upperRadical h F.Carrier (-x) := by
    rw [upperRadical_neg, hg, mul_inv_rev, mul_inv_cancel_left]
  have hqval : q = upperRadical h F.Carrier x * k⁻¹ := by
    rw [hg, mul_inv_cancel_right]
  have hkval : k = q⁻¹ * upperRadical h F.Carrier x := by
    rw [hg, inv_mul_cancel_left]
  -- entries of the diagonal blocks and of their inverses
  have hAinv' : ∀ a b : Fin (m 0 + 1), ((A⁻¹ : GeneralLinear (m 0 + 1) F.Carrier) :
        Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F.Carrier) a b =
      (q⁻¹ : GeneralLinear (t + 1) F.Carrier) ((succBlockShape m h).index 0 a)
        ((succBlockShape m h).index 0 b) := fun _ _ => rfl
  have hDinv' : ∀ a b : Fin (m 1 + 1), ((D⁻¹ : GeneralLinear (m 1 + 1) F.Carrier) :
        Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) F.Carrier) a b =
      (q⁻¹ : GeneralLinear (t + 1) F.Carrier) ((succBlockShape m h).index 1 a)
        ((succBlockShape m h).index 1 b) := fun _ _ => rfl
  have hD' : ∀ a b : Fin (m 1 + 1),
      (D : Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) F.Carrier) a b =
        (q : GeneralLinear (t + 1) F.Carrier) ((succBlockShape m h).index 1 a)
          ((succBlockShape m h).index 1 b) := fun _ _ => rfl
  have hAinv : ∀ a b : Fin (m 0 + 1), ((A⁻¹ : GeneralLinear (m 0 + 1) F.Carrier) :
        Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F.Carrier) a b =
      k ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 0 b) := by
    intro a b
    rw [hAinv', hqinv, mul_apply_index h, sum_mul_radical_zero_zero, sum_mul_radical_one_zero,
      add_zero]
  have hDval : ∀ a b : Fin (m 1 + 1),
      (D : Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) F.Carrier) a b =
        (k⁻¹ : GeneralLinear (t + 1) F.Carrier) ((succBlockShape m h).index 1 a)
          ((succBlockShape m h).index 1 b) := by
    intro a b
    rw [hD', hqval, mul_apply_index h, sum_radical_one_zero_mul, sum_radical_one_one_mul,
      zero_add]
  have hk01 : ∀ (a : Fin (m 0 + 1)) (b : Fin (m 1 + 1)),
      k ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 b) =
        ∑ c, ((A⁻¹ : GeneralLinear (m 0 + 1) F.Carrier) :
          Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F.Carrier) a c * x c b := by
    intro a b
    have hzero : ∀ c : Fin (m 1 + 1), (q⁻¹ : GeneralLinear (t + 1) F.Carrier)
        ((succBlockShape m h).index 0 a) ((succBlockShape m h).index 1 c) = 0 :=
      fun c => ((succBlockShape m h).mem_oppositeParabolic_iff F.Carrier _).1 (inv_mem hq) 0 1
        a c (show (0 : Fin 2) < 1 by decide)
    rw [hkval, mul_apply_index h, sum_mul_radical_zero_one]
    simp only [hzero, zero_mul, Finset.sum_const_zero, add_zero, hAinv']
  -- `x = A k₀₁`
  have hxA : x = (A : Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F.Carrier) *
      Matrix.of fun c b => k ((succBlockShape m h).index 0 c) ((succBlockShape m h).index 1 b) := by
    have hK : (Matrix.of fun c b =>
          k ((succBlockShape m h).index 0 c) ((succBlockShape m h).index 1 b)) =
        ((A⁻¹ : GeneralLinear (m 0 + 1) F.Carrier) :
          Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F.Carrier) * x := by
      ext c b
      rw [Matrix.of_apply, hk01, Matrix.mul_apply]
    rw [hK, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  -- the exponent `d`
  have hAinvInt : ∀ a b : Fin (m 0 + 1), ((A⁻¹ : GeneralLinear (m 0 + 1) F.Carrier) :
      Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F.Carrier) a b ∈ T.Integers := by
    intro a b
    rw [hAinv]
    exact hk'.1 _ _
  have hdetAinv : T.normalizedAbs (determinant A⁻¹ : F.Carrier) ≤ 1 := by
    rw [T.normalizedAbs_le_one_iff_mem_integers, Matrix.GeneralLinearGroup.val_det_apply]
    exact det_mem_of_forall_mem T.Integers _ hAinvInt
  have hprod : T.normalizedAbs (determinant A : F.Carrier) *
      T.normalizedAbs (determinant A⁻¹ : F.Carrier) = 1 := by
    rw [← T.normalizedAbs_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
      Units.val_one, T.normalizedAbs_one]
  have hge : 1 ≤ T.normalizedAbs (determinant A : F.Carrier) := by
    have hnn := T.normalizedAbs_nonneg (determinant A : F.Carrier)
    nlinarith [mul_nonneg hnn (sub_nonneg.2 hdetAinv)]
  have hord : 0 ≤ -T.ord (determinant A : F.Carrier) := by
    rw [T.normalizedAbs_of_ne_zero (determinant A).ne_zero] at hge
    exact (one_le_zpow_iff_right₀ hq1).1 hge
  set d := (-T.ord (determinant A : F.Carrier)).toNat with hd
  have hdz : (d : ℤ) = -T.ord (determinant A : F.Carrier) := Int.toNat_of_nonneg hord
  have hAnorm : T.normalizedAbs (determinant A : F.Carrier) =
      (T.residueCardinality : ℝ) ^ d := by
    rw [T.normalizedAbs_of_ne_zero (determinant A).ne_zero, ← hdz, zpow_natCast]
  have hϖnorm : T.normalizedAbs ((T.uniformizer : F.Carrier) ^ d) =
      ((T.residueCardinality : ℝ) ^ d)⁻¹ := by
    have h' := LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs T (d : ℤ)
    rwa [zpow_natCast, Units.val_pow_eq_pow_val, LocalFactor.PadicAbelian.uniformizerUnit_coe,
      zpow_neg, zpow_natCast] at h'
  have hϖint : (T.uniformizer : F.Carrier) ^ d ∈ T.Integers := by
    rw [← T.normalizedAbs_le_one_iff_mem_integers, hϖnorm]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hq1.le)
  have hϖdet : (T.uniformizer : F.Carrier) ^ d * (determinant A : F.Carrier) ∈ T.Integers := by
    rw [← T.normalizedAbs_le_one_iff_mem_integers, T.normalizedAbs_mul, hϖnorm, hAnorm,
      inv_mul_cancel₀ (by positivity)]
  have hAbd : ∀ a b : Fin (m 0 + 1), (T.uniformizer : F.Carrier) ^ d *
      (A : Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F.Carrier) a b ∈ T.Integers := by
    intro a b
    rw [val_eq_det_smul_adjugate_inv A, Matrix.smul_apply, smul_eq_mul, ← mul_assoc]
    exact mul_mem hϖdet (adjugate_mem_of_forall_mem T.Integers _ hAinvInt a b)
  have hbox : x ∈ box F (m 0 + 1) (m 1 + 1) d := by
    intro a b
    change (T.uniformizer : F.Carrier) ^ d * x a b ∈ T.Integers
    rw [hxA, Matrix.mul_apply, Finset.mul_sum]
    refine Subring.sum_mem _ fun c _ => ?_
    rw [Matrix.of_apply, ← mul_assoc]
    exact mul_mem (hAbd a c) (hk'.1 _ _)
  -- determinants of the two blocks
  have hkey : T.determinantNorm (m 0 + 1) A * T.determinantNorm (m 1 + 1) D = 1 := by
    have h1 : T.determinantNorm (t + 1) (upperRadical h F.Carrier x) = 1 := by
      change T.normalizedAbsUnits (determinant (upperRadical h F.Carrier x)) = 1
      rw [determinant_upperRadical, map_one]
    have h2 : T.determinantNorm (t + 1) k = 1 := by
      apply Units.ext
      apply NNReal.eq
      rw [T.determinantNorm_coe, normalizedAbs_determinant_eq_one F hk]
      rfl
    rw [hg, map_mul, h2, mul_one] at h1
    change T.normalizedAbsUnits (determinant (Q : GeneralLinear (t + 1) F.Carrier)) = 1 at h1
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
    · change (T.uniformizer : F.Carrier) ^ d *
        ((A⁻¹ : GeneralLinear (m 0 + 1) F.Carrier) :
          Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F.Carrier) a b ∈ T.Integers
      exact mul_mem hϖint (hAinvInt a b)
    · change (T.uniformizer : F.Carrier) ^ d *
        (D : Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) F.Carrier) a b ∈ T.Integers
      rw [hDval]
      exact mul_mem hϖint (hk'.2 _ _)
    · change (T.uniformizer : F.Carrier) ^ d *
        ((D⁻¹ : GeneralLinear (m 1 + 1) F.Carrier) :
          Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) F.Carrier) a b ∈ T.Integers
      rw [hDinv', hqinv, mul_apply_index h, sum_mul_radical_zero_one, sum_mul_radical_one_one,
        mul_add, Finset.mul_sum]
      refine add_mem (Subring.sum_mem _ fun c _ => ?_) (mul_mem hϖint (hk'.1 _ _))
      rw [Matrix.neg_apply, mul_neg, mul_neg, mul_left_comm]
      exact neg_mem (mul_mem (hk'.1 _ _) (hbox c b))
  · rw [← hAnorm']
    exact eq_inv_of_mul_eq_one_right hkeyR

end Padic

end Langlands.RankinSelberg.TwoBlockConvergence
