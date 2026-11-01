import Langlands.Representation.RankinSelberg.TwoBlockDominantLeviSupport

/-! # Endpoint bounds in a leading unequal-rank block -/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantRectangular

open scoped BigOperators
open GeneralLinear Whittaker HarmonicAnalysis TwoBlockDeformation TwoBlockConvergence
  TwoBlockLowerFixedSlice

universe uF uV

section Algebra

variable {K : Type uF} [Field K]

private theorem suffix_minor_mul {m : ℕ}
    (t : Fin m) (U A : Matrix (Fin m) (Fin m) K)
    (hU : U.IsUpperTriangular) (c : {i : Fin m // t ≤ i} → Fin m) :
    Matrix.det ((U * A).submatrix Subtype.val c) =
      (∏ i : {i : Fin m // t ≤ i}, U i i) *
        Matrix.det (A.submatrix Subtype.val c) := by
  classical
  have hm : (U * A).submatrix Subtype.val c =
      (U.submatrix Subtype.val Subtype.val :
        Matrix {i : Fin m // t ≤ i} {i : Fin m // t ≤ i} K) *
        A.submatrix Subtype.val c := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    apply Finset.sum_congr_set {q : Fin m | t ≤ q}
    · intro q hq
      rfl
    · intro q hq
      rw [hU (lt_of_lt_of_le (lt_of_not_ge hq) i.property), zero_mul]
  have hsub : (U.submatrix Subtype.val Subtype.val :
      Matrix {i : Fin m // t ≤ i} {i : Fin m // t ≤ i} K).IsUpperTriangular := by
    intro i j hij
    exact hU hij
  rw [hm, Matrix.det_mul, Matrix.det_of_isUpperTriangular hsub]
  rfl

private theorem det_mem_subring {ι : Type*} [Fintype ι] [DecidableEq ι]
    (O : Subring K) (A : Matrix ι ι K) (hA : ∀ i j, A i j ∈ O) :
    A.det ∈ O := by
  let B : Matrix ι ι O := fun i j => ⟨A i j, hA i j⟩
  have he : (B.map O.subtype) = A := rfl
  rw [← he]
  change (O.subtype.mapMatrix B).det ∈ O
  rw [← O.subtype.map_det]
  exact (B.det).property

private theorem unequalRankMatrix_identity_columns {n : ℕ} (j k : ℕ)
    (g : GeneralLinear (n + 1) K) (x : Matrix (Fin j) (Fin (n + 1)) K)
    (a b : Fin (n + (j + k + 1) + 1))
    (ha : n + 1 ≤ a.val) (hb : n + 1 ≤ b.val) :
    unequalRankMatrix j k g x a b = if a = b then 1 else 0 := by
  rw [unequalRankMatrix_val]
  simp [appendIdentity_entry, rectangularEntries, not_lt.mpr ha, not_lt.mpr hb]

/-- The principal suffix beginning at the last row of the leading group block
has determinant equal to that block's last diagonal entry. -/
theorem unequalRankMatrix_last_entry_minor {n : ℕ} (j k : ℕ)
    (g : GeneralLinear (n + 1) K) (x : Matrix (Fin j) (Fin (n + 1)) K) :
    let t : Fin (n + (j + k + 1) + 1) := ⟨n, by omega⟩
    Matrix.det ((unequalRankMatrix j k g x).val.submatrix
      (Subtype.val : {i // t ≤ i} → _) Subtype.val) =
      g (Fin.last n) (Fin.last n) := by
  classical
  dsimp only
  let t : Fin (n + (j + k + 1) + 1) := ⟨n, by omega⟩
  let S := {i : Fin (n + (j + k + 1) + 1) // t ≤ i}
  let t₀ : S := ⟨t, le_rfl⟩
  let B : Matrix S S K :=
    (unequalRankMatrix j k g x).val.submatrix Subtype.val Subtype.val
  change B.det = _
  have hd (i : S) (hi : i ≠ t₀) : B i i = 1 := by
    have hne : i.val ≠ t := fun h => hi (Subtype.ext h)
    have hn : n + 1 ≤ i.val.val := by
      have hle : n ≤ i.val.val := i.property
      have hneq : i.val.val ≠ n := fun h => hne (Fin.ext h)
      omega
    change unequalRankMatrix j k g x i.val i.val = 1
    rw [unequalRankMatrix_identity_columns j k g x i.val i.val hn hn]
    simp
  have hB : B.IsLowerTriangular := by
    intro i l hil
    have hl : n + 1 ≤ l.val.val := by
      have := i.property
      have hlt : i.val.val < l.val.val := hil
      change n ≤ i.val.val at this
      omega
    have hne : i.val ≠ l.val := by
      intro h
      have hlt : i.val.val < l.val.val := hil
      have he := congrArg Fin.val h
      omega
    change unequalRankMatrix j k g x i.val l.val = 0
    rw [unequalRankMatrix_val]
    simp [appendIdentity_entry, rectangularEntries, not_lt.mpr hl, hne]
  rw [Matrix.det_of_isLowerTriangular B hB]
  rw [Finset.prod_eq_single t₀ (fun i _ hi => hd i hi) (by simp)]
  change unequalRankMatrix j k g x t t = _
  rw [unequalRankMatrix_val]
  simp [appendIdentity_entry, rectangularEntries, t]
  rfl

end Algebra

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance endpointBoundsTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance endpointBoundsValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance endpointBoundsLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

/-- A principal suffix minor is bounded by the Iwasawa diagonal on that suffix. -/
theorem iwasawa_principal_suffix_minor_bound (r : ℕ)
    (u : GeneralLinear (r + 1) F.Carrier)
    (a : Fin (r + 1) → F.Carrierˣ) (κ : GeneralLinear (r + 1) F.Carrier)
    (hu : u ∈ upperUnipotent (r + 1) F.Carrier)
    (hκ : κ ∈ integralOpen F r) (t : Fin (r + 1)) :
    F.canonicalTopologicalData.normalizedAbs
      (Matrix.det ((u * Iwasawa.diagonalUnits a * κ).val.submatrix
        (Subtype.val : {i // t ≤ i} → _) Subtype.val)) ≤
      ∏ i : {i : Fin (r + 1) // t ≤ i},
        F.canonicalTopologicalData.normalizedAbs (a i : F.Carrier) := by
  classical
  have htri : (u * Iwasawa.diagonalUnits a).val.IsUpperTriangular := by
    intro i j hij
    change (u.val * (Iwasawa.diagonalUnits a).val) i j = 0
    rw [Iwasawa.diagonalUnits_val, Matrix.mul_diagonal, hu.1 hij, zero_mul]
  have hdiag (i : Fin (r + 1)) :
      (u * Iwasawa.diagonalUnits a) i i = (a i : F.Carrier) := by
    change (u.val * (Iwasawa.diagonalUnits a).val) i i = _
    rw [Iwasawa.diagonalUnits_val, Matrix.mul_diagonal, hu.2 i, one_mul]
  have hdet : (κ.val.submatrix
      (Subtype.val : {i : Fin (r + 1) // t ≤ i} → _) Subtype.val).det ∈
      F.canonicalTopologicalData.Integers :=
    det_mem_subring _ _ fun i l => ((mem_integralOpen F κ).mp hκ).1 i l
  have hle := (F.canonicalTopologicalData.normalizedAbs_le_one_iff_mem_integers _).mpr hdet
  change F.canonicalTopologicalData.normalizedAbs
    (Matrix.det (((u * Iwasawa.diagonalUnits a).val * κ.val).submatrix
      (Subtype.val : {i // t ≤ i} → _) Subtype.val)) ≤ _
  rw [suffix_minor_mul t _ _ htri Subtype.val]
  simp_rw [hdiag]
  rw [F.canonicalTopologicalData.normalizedAbs_mul, normalizedAbs_prod F]
  exact (mul_le_mul_of_nonneg_left hle
    (Finset.prod_nonneg fun i _ => F.canonicalTopologicalData.normalizedAbs_nonneg _)).trans_eq
      (mul_one _)

/-- A bounded adjacent Iwasawa ratio and the terminal identity row bound the
last entry of the original leading group block. -/
theorem unequalRankMatrix_last_entry_bound (n j k : ℕ)
    (g : GeneralLinear (n + 1) F.Carrier)
    (x : Matrix (Fin j) (Fin (n + 1)) F.Carrier)
    (u : GeneralLinear (n + (j + k + 1) + 1) F.Carrier)
    (a : Fin (n + (j + k + 1) + 1) → F.Carrierˣ)
    (κ : GeneralLinear (n + (j + k + 1) + 1) F.Carrier)
    (hu : u ∈ upperUnipotent (n + (j + k + 1) + 1) F.Carrier)
    (hκ : κ ∈ integralOpen F (n + (j + k + 1)))
    (he : unequalRankMatrix j k g x = u * Iwasawa.diagonalUnits a * κ)
    (B : ℝ) (hB : 1 ≤ B)
    (hroot : ∀ i : Fin (n + (j + k + 1)),
      F.canonicalTopologicalData.normalizedAbs
        ((a i.castSucc / a i.succ : F.Carrierˣ) : F.Carrier) ≤ B) :
    F.canonicalTopologicalData.normalizedAbs (g (Fin.last n) (Fin.last n)) ≤
      (B ^ (n + (j + k + 1))) ^ (n + (j + k + 1) + 1) := by
  classical
  have hrow (b : Fin (n + (j + k + 1) + 1)) :
      unequalRankMatrix j k g x (Fin.last (n + (j + k + 1))) b =
        if Fin.last (n + (j + k + 1)) = b then 1 else 0 := by
    rw [unequalRankMatrix_val]
    simp [appendIdentity_entry, rectangularEntries, Fin.val_last,
      show ¬n + (j + k + 1) < n + 1 by omega,
      show ¬n + (j + k + 1) < n + 1 + j by omega]
  have hlast := diagonal_abs_last F F.canonicalTopologicalData
    (n + (j + k + 1)) _ u a κ hrow hu
    ((Conductor.mem_integralSubgroup _ _ κ).mpr ((mem_integralOpen F κ).mp hκ)) he
  have hdiag := diagonal_abs_bound F F.canonicalTopologicalData
    (n + (j + k + 1)) a B hB hlast hroot
  let t : Fin (n + (j + k + 1) + 1) := ⟨n, by omega⟩
  let S := {i : Fin (n + (j + k + 1) + 1) // t ≤ i}
  have hminor := iwasawa_principal_suffix_minor_bound F
    (n + (j + k + 1)) u a κ hu hκ t
  rw [← he, unequalRankMatrix_last_entry_minor] at hminor
  have hprod :
      (∏ i : S, F.canonicalTopologicalData.normalizedAbs (a i : F.Carrier)) ≤
        (B ^ (n + (j + k + 1))) ^ Fintype.card S := by
    calc
      _ ≤ ∏ _i : S, B ^ (n + (j + k + 1)) :=
        Finset.prod_le_prod₀ (fun i _ => F.canonicalTopologicalData.normalizedAbs_nonneg _)
          (fun i _ => hdiag i)
      _ = _ := by simp
  have hcard : Fintype.card S ≤ n + (j + k + 1) + 1 :=
    (Fintype.card_le_of_injective (Subtype.val : S → _) Subtype.val_injective).trans_eq
      (Fintype.card_fin _)
  exact hminor.trans (hprod.trans
    (pow_le_pow_right₀ (one_le_pow₀ hB) hcard))

/-- An endpoint entry bound uniform in the rectangle, the other invertible
diagonal block and the right integral factor. -/
def IsBlockSumLastEntryBound (ψ : UnitaryAdditiveCharacter F.Carrier)
    (n j k d : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ
      (GeneralLinear (n + (j + k + 1) + 1 + (d + 1)) F.Carrier) V)
    (ell : glFunctionals ψ (n + (j + k + 1) + 1 + d) π)
    (W : (coefficientModel π ell).toSubmodule) (B : ℝ) : Prop :=
  1 ≤ B ∧ ∀ (g : GeneralLinear (n + 1) F.Carrier)
    (x : Matrix (Fin j) (Fin (n + 1)) F.Carrier)
    (D : GeneralLinear (d + 1) F.Carrier)
    (c : GeneralLinear (n + (j + k + 1) + 1 + (d + 1)) F.Carrier),
    c ∈ integralOpen F (n + (j + k + 1) + 1 + d) →
    W.val.val (blockSum (unequalRankMatrix j k g x, D) * c) ≠ 0 →
    F.canonicalTopologicalData.normalizedAbs (g (Fin.last n) (Fin.last n)) ≤ B

/-- A smooth ambient coefficient uniformly bounds the leading endpoint entry. -/
theorem exists_blockSum_last_entry_bound (ψ : UnitaryAdditiveCharacter F.Carrier)
    (n j k d : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ
      (GeneralLinear (n + (j + k + 1) + 1 + (d + 1)) F.Carrier) V)
    (hπ : IsSmooth π) (ell : glFunctionals ψ (n + (j + k + 1) + 1 + d) π)
    (W : (coefficientModel π ell).toSubmodule) :
    ∃ B, IsBlockSumLastEntryBound F ψ n j k d π ell W B := by
  obtain ⟨L, hL⟩ := exists_coefficient_blockSum_rootBounded F ψ π hπ ell W
  have hq : (1 : ℝ) ≤ F.canonicalTopologicalData.residueCardinality := by
    exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one.le
  refine ⟨(((F.canonicalTopologicalData.residueCardinality : ℝ) ^ L) ^
    (n + (j + k + 1))) ^ (n + (j + k + 1) + 1),
    one_le_pow₀ (one_le_pow₀ (one_le_pow₀ hq)),
    fun g x D c hc hW => ?_⟩
  obtain ⟨uA, uB, lam, mu, kA, kB, huA, huB, hkA, hkB, heA, heB, hrA, hrB⟩ :=
    hL (unequalRankMatrix j k g x) D c hc hW
  exact unequalRankMatrix_last_entry_bound F n j k g x uA
    (fun i => LocalFactor.PadicAbelian.uniformizerUnit F.canonicalTopologicalData ^ lam i)
    kA huA hkA heA _ (one_le_pow₀ hq)
    (normalizedAbs_ratios_of_rootBounded F hrA)

theorem exists_reindex_blockSum_last_entry_bound
    (ψ : UnitaryAdditiveCharacter F.Carrier) (n j k d r : ℕ)
    (H : n + (j + k + 1) + 1 + (d + 1) = r + 1)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hπ : IsSmooth π) (ell : glFunctionals ψ r π)
    (W : (coefficientModel π ell).toSubmodule) :
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ (g : GeneralLinear (n + 1) F.Carrier)
        (Y : Matrix (Fin j) (Fin (n + 1)) F.Carrier)
        (D : GeneralLinear (d + 1) F.Carrier)
        (c : GeneralLinear (r + 1) F.Carrier),
        c ∈ integralOpen F r →
        W.val.val (reindex (finCongr H) (blockSum (unequalRankMatrix j k g Y, D)) * c) ≠ 0 →
        F.canonicalTopologicalData.normalizedAbs (g (Fin.last n) (Fin.last n)) ≤ B := by
  have hr : r = n + (j + k + 1) + 1 + d := by omega
  subst r
  exact exists_blockSum_last_entry_bound F ψ n j k d π hπ ell W

variable {t r j k : ℕ} {m : Fin 2 → ℕ}

/-- A bound for the actual second Levi block's terminal diagonal entry whenever
the coefficient at the actual dominant matrix is nonzero. -/
def IsLeviSecondEndpointBound
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (ell : glFunctionals ψ r π) (W : (coefficientModel π ell).toSubmodule)
    (B : ℝ) : Prop :=
  1 ≤ B ∧ ∀ (b : (succBlockShape m h).Levi F.Carrier)
    (c : GeneralLinear (t + 1) F.Carrier)
    (x : Matrix (Fin (m 0 + 1)) (Fin k) F.Carrier)
    (y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier),
    c ∈ integralOpen F t →
    W.val.val (matrix h hr ((succBlockShape m h).leviEmbedding F.Carrier b * c) x y) ≠ 0 →
    F.canonicalTopologicalData.normalizedAbs
      (b 1 (Fin.last (m 1)) (Fin.last (m 1))) ≤ B

/-- The actual second endpoint bound holds for every smooth ambient coefficient. -/
theorem exists_levi_second_endpoint_bound
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (h : ∑ i, (m i + 1) = t + 1) (hr : r = t + (j + k + 1))
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hπ : IsSmooth π) (ell : glFunctionals ψ r π)
    (W : (coefficientModel π ell).toSubmodule) :
    ∃ B, IsLeviSecondEndpointBound F ψ h hr π ell W B := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_reindex_blockSum_last_entry_bound F ψ (m 1) j 0 (k + m 0) r
      (diagonalBlocksRank h hr) π hπ ell W
  refine ⟨B, hB, fun b c x y hc hW => ?_⟩
  have he : matrix h hr ((succBlockShape m h).leviEmbedding F.Carrier b * c) x y =
      reindex (finCongr (diagonalBlocksRank h hr))
        (blockSum (unequalRankMatrix j 0 (b 1)
          (y.submatrix Fin.rev Fin.rev * (b 1).val),
          trailingBlock (b 0) (x.submatrix Fin.rev Fin.rev))) *
        (diagonalRightPermutation h hr * append hr c) := by
    rw [← matrix_levi_diagonalBlocks h hr b x y]
    simp only [matrix, map_mul, mul_assoc, inv_mul_cancel_left]
  apply hbound (b 1) (y.submatrix Fin.rev Fin.rev * (b 1).val)
    (trailingBlock (b 0) (x.submatrix Fin.rev Fin.rev))
    (diagonalRightPermutation h hr * append hr c)
    ((integralOpen F r).mul_mem (diagonalRightPermutation_mem_integralOpen F h hr)
      (append_mem_integralOpen F hr hc))
  simpa only [← he] using hW

end Langlands.RankinSelberg.TwoBlockDominantRectangular
