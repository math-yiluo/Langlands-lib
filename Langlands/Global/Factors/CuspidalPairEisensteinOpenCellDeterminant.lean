import Langlands.Global.Factors.CuspidalPairEisensteinOpenCellMajorant
import Langlands.Global.Factors.CuspidalPairEisensteinOneplace
import Langlands.Global.Factors.CuspidalPairSchemeSeries
import Langlands.Global.ArchimedeanCompact
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-! # The second Levi block on the open cell

Let `g = w u'(Y) = p k` with `p` in the upper parabolic of block sizes `(r + 1, t + 1)` and `k`
in the standard maximal compact subgroup, and let `m₂` be the second diagonal block of `p`.
The last `t + 1` rows of `g` are `[I_(t+1) | Y]`, so the last `t + 1` rows of `k = p⁻¹ g` are
`[A | A Y]` with `A = m₂⁻¹`. Since the entries of `k` are integral at the finite places and
bounded by `1` at the archimedean places, `|det m₂|_v ≥ max(1, ‖Y_v‖)` at every finite place
and `|det m₂|_v ≥ max(1, ‖Y_v‖) / c_t` at every archimedean place. For `e ≥ 0`, raising these
lower bounds to the power `-e` reverses them and bounds `|det m₂|_𝔸^(-e)` by a constant times
the majorant `Ω_e(Y)`. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false

universe u

open NumberField IsDedekindDomain
open scoped Classical

namespace Langlands.Global.CuspidalPairEisenstein.OpenCellDeterminant

open Langlands.GeneralLinear AdelicBlockParabolic PrimitiveAdelicHeight

variable {F : Type u} [Field F] [NumberField F] {r t : ℕ}

section Rows

variable (r) in
/-- The rows of the second diagonal block, `r + 1 + a` for `a < t + 1`. -/
abbrev rowIndex (a : Fin (t + 1)) : Fin (r + t + 2) :=
  (blockShape r t).index (secondBlock r t) a

theorem rowIndex_val (a : Fin (t + 1)) : (rowIndex r a : ℕ) = r + 1 + a := by
  change ((blockShape r t).indexEquiv ⟨secondBlock r t, a⟩).val = r + 1 + a.val
  rw [BlockShape.indexEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
    finSigmaFinEquiv_apply]
  change (∑ k : Fin 1, ![r + 1, t + 1] (Fin.castLE (by decide : 1 ≤ 2) k)) + a.val =
    r + 1 + a.val
  rw [Fin.sum_univ_one]
  rfl

variable (r) in
/-- The first `t + 1` columns. -/
abbrev leftColumn (j : Fin (t + 1)) : Fin (r + t + 2) := ⟨j, by omega⟩

variable (t) in
/-- The last `r + 1` columns, `t + 1 + j` for `j < r + 1`. -/
abbrev rightColumn (j : Fin (r + 1)) : Fin (r + t + 2) := ⟨t + 1 + j, by omega⟩

theorem openCellWeyl_rowIndex_apply (a : Fin (t + 1)) (d : Fin (r + t + 2)) :
    (openCellWeyl F r t : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F))
        (rowIndex r a) d = if (d : ℕ) = a then 1 else 0 := by
  change Shahidi.blockWeyl (r + 1) (t + 1) (Adeles F) (Fin.cast (by omega) (rowIndex r a))
    (Fin.cast (by omega) d) = _
  have hi : (Fin.cast (by omega) (rowIndex r a) : Fin (r + 1 + (t + 1))) = a.natAdd (r + 1) :=
    Fin.ext (by simp [rowIndex_val])
  rw [hi, Shahidi.blockWeyl_entry]
  have hiff : Shahidi.blockWeylPermutation (r + 1) (t + 1) (Fin.cast (by omega) d) =
      a.natAdd (r + 1) ↔ (d : ℕ) = a := by
    rw [← Equiv.eq_symm_apply, Shahidi.blockWeylPermutation_symm_second, Fin.ext_iff]
    simp
  exact if_congr hiff rfl rfl

/-- Left multiplication by `w` moves row `a` of `M` to row `r + 1 + a`. -/
theorem openCellWeyl_mul_rowIndex_apply (M : AdelicGL F (r + t + 2)) (a : Fin (t + 1))
    (c : Fin (r + t + 2)) :
    ((openCellWeyl F r t * M : AdelicGL F (r + t + 2)) :
        Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) (rowIndex r a) c =
      (M : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) (leftColumn r a) c := by
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (leftColumn r a)]
  · rw [openCellWeyl_rowIndex_apply, ite_eq_left rfl, one_mul]
  · intro d _ hd
    rw [openCellWeyl_rowIndex_apply, ite_eq_right, zero_mul]
    intro h
    exact hd (Fin.ext h)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem openCell_rowIndex_leftColumn (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F))
    (a j : Fin (t + 1)) :
    ((openCellWeyl F r t * openCellUnipotent F r t Y : AdelicGL F (r + t + 2)) :
        Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) (rowIndex r a) (leftColumn r j) =
      if a = j then 1 else 0 := by
  rw [openCellWeyl_mul_rowIndex_apply, openCellUnipotent_apply]
  have h1 : (Fin.cast (by omega) (leftColumn r a) : Fin (t + 1 + (r + 1))) = a.castAdd (r + 1) :=
    Fin.ext rfl
  have h2 : (Fin.cast (by omega) (leftColumn r j) : Fin (t + 1 + (r + 1))) = j.castAdd (r + 1) :=
    Fin.ext rfl
  rw [h1, h2, Shahidi.upper_first_first]

theorem openCell_rowIndex_rightColumn (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F))
    (a : Fin (t + 1)) (j : Fin (r + 1)) :
    ((openCellWeyl F r t * openCellUnipotent F r t Y : AdelicGL F (r + t + 2)) :
        Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) (rowIndex r a) (rightColumn t j) =
      Y a j := by
  rw [openCellWeyl_mul_rowIndex_apply, openCellUnipotent_apply]
  have h1 : (Fin.cast (by omega) (leftColumn r a) : Fin (t + 1 + (r + 1))) = a.castAdd (r + 1) :=
    Fin.ext rfl
  have h2 : (Fin.cast (by omega) (rightColumn t j) : Fin (t + 1 + (r + 1))) =
      j.natAdd (t + 1) := Fin.ext rfl
  rw [h1, h2, Shahidi.upper_first_second]

/-- The inverse `A = m₂⁻¹` of the second diagonal block of `p`. -/
abbrev blockInverse (p : Full F (blockShape r t)) :
    Matrix (Fin (t + 1)) (Fin (t + 1)) (Adeles F) :=
  (((Oneplace.leviSnd ((blockShape r t).leviProjection (Adeles F) p))⁻¹ : AdelicGL F (t + 1)) :
    Matrix (Fin (t + 1)) (Fin (t + 1)) (Adeles F))

/-- The rows `r + 1 + a` of `k = p⁻¹ g` are `A` times the corresponding rows of `g`. -/
theorem rowIndex_apply_of_mul_eq {p : Full F (blockShape r t)} {k g : AdelicGL F (r + t + 2)}
    (hpk : p.val * k = g) (a : Fin (t + 1)) (c : Fin (r + t + 2)) :
    (k : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) (rowIndex r a) c =
      ∑ e, blockInverse p a e *
        (g : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) (rowIndex r e) c := by
  have hk : k = (p⁻¹ : Full F (blockShape r t)).val * g := by
    rw [← hpk, Subgroup.coe_inv, inv_mul_cancel_left]
  rw [hk, Units.val_mul, Matrix.mul_apply, ← (blockShape r t).indexEquiv.sum_comp,
    Fintype.sum_sigma, Finset.sum_eq_single (secondBlock r t)]
  · refine Finset.sum_congr rfl fun e _ => ?_
    congr 1
  · intro i _ hi
    have hi' : i = firstBlock r t := (eq_firstBlock_or_eq_secondBlock r t i).resolve_right hi
    subst hi'
    refine Finset.sum_eq_zero fun e _ => ?_
    have h0 := ((blockShape r t).mem_parabolic_iff (Adeles F) _).mp (p⁻¹).property
      (secondBlock r t) (firstBlock r t) a e (Fin.mk_lt_mk.mpr Nat.zero_lt_one)
    change (p⁻¹ : Full F (blockShape r t)).val.val (rowIndex r a)
      ((blockShape r t).index (firstBlock r t) e) * _ = 0
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem compact_rowIndex_leftColumn {p : Full F (blockShape r t)} {k : AdelicGL F (r + t + 2)}
    {Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)}
    (hpk : p.val * k = openCellWeyl F r t * openCellUnipotent F r t Y) (a j : Fin (t + 1)) :
    (k : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) (rowIndex r a) (leftColumn r j) =
      blockInverse p a j := by
  rw [rowIndex_apply_of_mul_eq hpk]
  simp only [openCell_rowIndex_leftColumn, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem compact_rowIndex_rightColumn {p : Full F (blockShape r t)} {k : AdelicGL F (r + t + 2)}
    {Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)}
    (hpk : p.val * k = openCellWeyl F r t * openCellUnipotent F r t Y) (a : Fin (t + 1))
    (j : Fin (r + 1)) :
    (k : Matrix (Fin (r + t + 2)) (Fin (r + t + 2)) (Adeles F)) (rowIndex r a) (rightColumn t j) =
      (blockInverse p * Y) a j := by
  rw [rowIndex_apply_of_mul_eq hpk, Matrix.mul_apply]
  simp only [openCell_rowIndex_rightColumn]

end Rows

section Finite

open OpenCellExhaustion OpenCellMajorant

variable (v : FinitePlace F)

/-- Entries of an element of the standard maximal compact subgroup are integral at every finite
place. -/
theorem finiteProjection_mem_of_mem_standardCompact {n : ℕ} {k : AdelicGL F n}
    (hk : k ∈ standardCompact F n) (i j : Fin n) :
    finiteProjection F v (k i j) ∈ v.adicCompletionIntegers F :=
  ((FiniteAdelicGL.mem_standardIntegral F n _).mp ((mem_standardCompact_iff F n k).mp hk).2).1
    i j v

/-- A matrix with integral entries has integral determinant and adjugate. -/
theorem norm_det_le_one_and_adjugate {m : ℕ} (M : Matrix (Fin m) (Fin m) (FiniteCompletion F v))
    (hM : ∀ i j, M i j ∈ v.adicCompletionIntegers F) :
    ‖M.det‖ ≤ 1 ∧ ∀ i j, ‖M.adjugate i j‖ ≤ 1 := by
  set O := v.adicCompletionIntegers F
  let MO : Matrix (Fin m) (Fin m) O := fun i j => ⟨M i j, hM i j⟩
  have hMO : O.subtype.mapMatrix MO = M := rfl
  constructor
  · rw [← hMO, ← RingHom.map_det]
    exact (norm_le_one_iff_mem_integers _).2 (MO.det).property
  · intro i j
    rw [← hMO, ← RingHom.map_adjugate]
    exact (norm_le_one_iff_mem_integers _).2 (MO.adjugate i j).property

theorem finiteProjection_mapMatrix_mul {a b c : ℕ} (M : Matrix (Fin a) (Fin b) (Adeles F))
    (N : Matrix (Fin b) (Fin c) (Adeles F)) :
    (M * N).map (finiteProjection F v) = M.map (finiteProjection F v) * N.map (finiteProjection F v) :=
  Matrix.map_mul

/-- **Finite places.** If `w u'(Y) = p k` with `k` in the standard maximal compact subgroup,
then `|det m₂|_v ≥ max(1, ‖Y_v‖)` at every finite place. -/
theorem max_one_entryNorm_le_norm_det {p : Full F (blockShape r t)} {k : AdelicGL F (r + t + 2)}
    {Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)}
    (hk : k ∈ standardCompact F (r + t + 2))
    (hpk : p.val * k = openCellWeyl F r t * openCellUnipotent F r t Y) :
    max 1 (entryNorm (matrixComponent v Y)) ≤
      ‖((Oneplace.leviSnd ((blockShape r t).leviProjection (Adeles F) p) : AdelicGL F (t + 1)) :
        Matrix (Fin (t + 1)) (Fin (t + 1)) (Adeles F)).map (finiteProjection F v) |>.det‖ := by
  set m₂ := Oneplace.leviSnd ((blockShape r t).leviProjection (Adeles F) p)
  set Av := (blockInverse p).map (finiteProjection F v) with hAv
  have hA : ∀ a j, Av a j ∈ v.adicCompletionIntegers F := fun a j => by
    rw [hAv, Matrix.map_apply, ← compact_rowIndex_leftColumn hpk]
    exact finiteProjection_mem_of_mem_standardCompact v hk _ _
  have hAY : ∀ a j, (Av * matrixComponent v Y) a j ∈ v.adicCompletionIntegers F := fun a j => by
    have h : Av * matrixComponent v Y = (blockInverse p * Y).map (finiteProjection F v) :=
      (finiteProjection_mapMatrix_mul v (blockInverse p) Y).symm
    rw [h, Matrix.map_apply, ← compact_rowIndex_rightColumn hpk]
    exact finiteProjection_mem_of_mem_standardCompact v hk _ _
  obtain ⟨hdet, hadj⟩ := norm_det_le_one_and_adjugate v Av hA
  have hprod : (m₂.val.map (finiteProjection F v)).det * Av.det = 1 := by
    rw [← Matrix.det_mul, hAv, ← finiteProjection_mapMatrix_mul]
    have h1 : m₂.val * blockInverse p = 1 := by
      change m₂.val * (m₂⁻¹).val = 1
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [h1, Matrix.map_one _ (map_zero _) (map_one _), Matrix.det_one]
  have hAv0 : Av.det ≠ 0 := right_ne_zero_of_mul_eq_one hprod
  have hnorm : ‖(m₂.val.map (finiteProjection F v)).det‖ = ‖Av.det‖⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← norm_mul, hprod, norm_one]
  have hpos : 0 < ‖Av.det‖ := norm_pos_iff.mpr hAv0
  rw [hnorm]
  refine max_le (one_le_inv₀ hpos |>.mpr hdet) ?_
  refine (entryNorm_le_iff (inv_nonneg.mpr hpos.le)).2 fun a j => ?_
  rw [← one_div, le_div_iff₀ hpos, mul_comm, ← norm_mul]
  have hY : Av.det • matrixComponent v Y = Av.adjugate * (Av * matrixComponent v Y) := by
    rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have hentry := congrFun (congrFun hY a) j
  rw [Matrix.smul_apply, smul_eq_mul] at hentry
  rw [hentry, Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun l _ => ?_
  rw [norm_mul]
  exact (mul_le_mul (hadj a l) ((norm_le_one_iff_mem_integers _).2 (hAY l j)) (norm_nonneg _)
    zero_le_one).trans_eq (one_mul 1)

end Finite

section Infinite

open InfinitePlace.Completion

/-- Entries of an element of the standard maximal compact subgroup have norm at most `1` at every
archimedean place: they are entries of real orthogonal or complex unitary matrices. -/
theorem norm_infiniteProjection_le_one {n : ℕ} {k : AdelicGL F n}
    (hk : k ∈ standardCompact F n) (i j : Fin n) (v : InfinitePlace F) :
    ‖infiniteProjection F v (k i j)‖ ≤ 1 := by
  obtain ⟨q, hq⟩ := ((mem_standardCompact_iff F n k).mp hk).1
  have hmix : InfiniteAdeleRing.ringEquiv_mixedSpace F (k i j).1 =
      (fun w => (q.1 w : Matrix (Fin n) (Fin n) ℝ) i j,
        fun w => (q.2 w : Matrix (Fin n) (Fin n) ℂ) i j) := by
    have h1 : (k i j).1 = (AdelicGL.infinite F n k) i j := rfl
    rw [h1, ← hq]
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _
  change ‖(k i j).1 v‖ ≤ 1
  by_cases hv : v.IsReal
  · have h := congrArg (fun x => x.1 ⟨v, hv⟩) hmix
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at h
    rw [← (isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero (map_zero _), h]
    exact entry_norm_bound_of_unitary (q.1 ⟨v, hv⟩).property i j
  · have hc : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hv
    have h := congrArg (fun x => x.2 ⟨v, hc⟩) hmix
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at h
    rw [← (isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _), h]
    exact entry_norm_bound_of_unitary (q.2 ⟨v, hc⟩).property i j

/-- Over a normed field, a matrix with entries of norm at most `1` has determinant and adjugate
entries of norm at most `m!`. -/
theorem norm_det_le_factorial_and_adjugate {K : Type*} [NormedField K] {m : ℕ}
    (M : Matrix (Fin m) (Fin m) K) (hM : ∀ i j, ‖M i j‖ ≤ 1) :
    ‖M.det‖ ≤ m.factorial ∧ ∀ i j, ‖M.adjugate i j‖ ≤ m.factorial := by
  have hdet : ∀ N : Matrix (Fin m) (Fin m) K, (∀ i j, ‖N i j‖ ≤ 1) →
      ‖N.det‖ ≤ m.factorial := by
    intro N hN
    have h := Matrix.det_le (abv := NormedField.toAbsoluteValue K) (x := 1) hN
    rw [Fintype.card_fin, one_pow, nsmul_eq_mul, mul_one] at h
    exact h
  refine ⟨hdet M hM, fun i j => ?_⟩
  rw [Matrix.adjugate_apply]
  refine hdet _ fun a b => ?_
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]
    split_ifs
    · exact norm_one.le
    · rw [norm_zero]
      exact zero_le_one
  · exact hM a b

/-- The maximum norm of the entries of an adelic matrix at an archimedean place. -/
def archEntryNorm {a b : ℕ} (v : InfinitePlace F) (Y : Matrix (Fin a) (Fin b) (Adeles F)) : ℝ :=
  ‖fun i j => infiniteProjection F v (Y i j)‖

theorem norm_le_archEntryNorm {a b : ℕ} (v : InfinitePlace F)
    (Y : Matrix (Fin a) (Fin b) (Adeles F)) (i : Fin a) (j : Fin b) :
    ‖infiniteProjection F v (Y i j)‖ ≤ archEntryNorm v Y :=
  (norm_le_pi_norm (fun j => infiniteProjection F v (Y i j)) j).trans
    (norm_le_pi_norm (fun i j => infiniteProjection F v (Y i j)) i)

theorem archEntryNorm_le_iff {a b : ℕ} (v : InfinitePlace F)
    (Y : Matrix (Fin a) (Fin b) (Adeles F)) {C : ℝ} (hC : 0 ≤ C) :
    archEntryNorm v Y ≤ C ↔ ∀ i j, ‖infiniteProjection F v (Y i j)‖ ≤ C := by
  unfold archEntryNorm
  rw [pi_norm_le_iff_of_nonneg hC]
  exact forall_congr' fun i => pi_norm_le_iff_of_nonneg hC

/-- **Archimedean places.** If `w u'(Y) = p k` with `k` in the standard maximal compact
subgroup, then `max(1, ‖Y_v‖) ≤ (t + 2)! |det m₂|_v` at every archimedean place. -/
theorem max_one_archEntryNorm_le_norm_det (v : InfinitePlace F) {p : Full F (blockShape r t)}
    {k : AdelicGL F (r + t + 2)} {Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)}
    (hk : k ∈ standardCompact F (r + t + 2))
    (hpk : p.val * k = openCellWeyl F r t * openCellUnipotent F r t Y) :
    max 1 (archEntryNorm v Y) ≤ ((t + 2).factorial : ℝ) *
      ‖((Oneplace.leviSnd ((blockShape r t).leviProjection (Adeles F) p) : AdelicGL F (t + 1)) :
        Matrix (Fin (t + 1)) (Fin (t + 1)) (Adeles F)).map (infiniteProjection F v) |>.det‖ := by
  set m₂ := Oneplace.leviSnd ((blockShape r t).leviProjection (Adeles F) p)
  set Av := (blockInverse p).map (infiniteProjection F v) with hAv
  set Yv := Y.map (infiniteProjection F v) with hYv
  have hA : ∀ a j, ‖Av a j‖ ≤ 1 := fun a j => by
    rw [hAv, Matrix.map_apply, ← compact_rowIndex_leftColumn hpk]
    exact norm_infiniteProjection_le_one hk _ _ v
  have hAY : ∀ a j, ‖(Av * Yv) a j‖ ≤ 1 := fun a j => by
    have h : Av * Yv = (blockInverse p * Y).map (infiniteProjection F v) := Matrix.map_mul.symm
    rw [h, Matrix.map_apply, ← compact_rowIndex_rightColumn hpk]
    exact norm_infiniteProjection_le_one hk _ _ v
  obtain ⟨hdet, hadj⟩ := norm_det_le_factorial_and_adjugate Av hA
  have hprod : (m₂.val.map (infiniteProjection F v)).det * Av.det = 1 := by
    rw [← Matrix.det_mul, hAv, ← Matrix.map_mul]
    have h1 : m₂.val * blockInverse p = 1 := by
      change m₂.val * (m₂⁻¹).val = 1
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [h1, Matrix.map_one _ (map_zero _) (map_one _), Matrix.det_one]
  have hAv0 : Av.det ≠ 0 := right_ne_zero_of_mul_eq_one hprod
  have hnorm : ‖(m₂.val.map (infiniteProjection F v)).det‖ = ‖Av.det‖⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← norm_mul, hprod, norm_one]
  have hpos : 0 < ‖Av.det‖ := norm_pos_iff.mpr hAv0
  have hfac : ((t + 1).factorial : ℝ) ≤ (t + 2).factorial := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ _)
  have hfac2 : ((t + 1 : ℕ) : ℝ) * (t + 1).factorial ≤ (t + 2).factorial := by
    rw [Nat.factorial_succ (t + 1)]
    push_cast
    nlinarith [(Nat.cast_nonneg (t + 1).factorial : (0 : ℝ) ≤ _)]
  rw [hnorm, ← div_eq_mul_inv]
  refine max_le ?_ ?_
  · rw [le_div_iff₀ hpos, one_mul]
    exact hdet.trans hfac
  refine (archEntryNorm_le_iff v Y (div_nonneg (Nat.cast_nonneg _) hpos.le)).2 fun a j => ?_
  rw [le_div_iff₀ hpos, mul_comm, ← norm_mul]
  have hY : Av.det • Yv = Av.adjugate * (Av * Yv) := by
    rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
  have hentry := congrFun (congrFun hY a) j
  rw [Matrix.smul_apply, smul_eq_mul] at hentry
  change ‖Av.det * Yv a j‖ ≤ _
  rw [hentry, Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ l, ‖Av.adjugate a l * (Av * Yv) l j‖ ≤ ∑ _l : Fin (t + 1), ((t + 1).factorial : ℝ) :=
        Finset.sum_le_sum fun l _ => by
          rw [norm_mul]
          exact (mul_le_mul (hadj a l) (hAY l j) (norm_nonneg _) (Nat.cast_nonneg _)).trans_eq
            (mul_one _)
    _ = ((t + 1 : ℕ) : ℝ) * (t + 1).factorial := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ _ := hfac2

end Infinite

section Global

open OpenCellExhaustion OpenCellMajorant InfinitePlace.Completion

/-- `absDet` is the product of the local determinant norms, with the archimedean multiplicities. -/
theorem absDet_eq_prod {n : ℕ} (m : AdelicGL F n) :
    absDet F n m =
      (∏ v : InfinitePlace F, ‖(m.val.map (infiniteProjection F v)).det‖ ^ v.mult) *
        ∏ᶠ v : FinitePlace F, ‖(m.val.map (finiteProjection F v)).det‖ := by
  rw [absDet, IdeleAbsoluteValue.coe_full]
  congr 1
  · refine Finset.prod_congr rfl fun v _ => ?_
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  · refine finprod_congr fun v => ?_
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl

theorem mulSupport_norm_det_finite {n : ℕ} (m : AdelicGL F n) :
    (Function.mulSupport fun v : FinitePlace F =>
      ‖(m.val.map (finiteProjection F v)).det‖).Finite := by
  have h := NumberField.FiniteAdeleRing.hasFiniteMulSupport_norm
    (ideleProductEquiv F (AdelicGL.determinant F n m)).2
  have heq : (fun v : FinitePlace F => ‖(m.val.map (finiteProjection F v)).det‖) =
      fun v => ‖((ideleProductEquiv F (AdelicGL.determinant F n m)).2 : FiniteAdeles F) v‖ := by
    funext v
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rfl
  rw [heq]
  exact h

theorem mulSupport_max_one_entryNorm_finite (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :
    (Function.mulSupport fun v : FinitePlace F =>
      max 1 (entryNorm (matrixComponent v Y))).Finite := by
  obtain ⟨A, hA⟩ := exists_mem_integralOutside (r := r) (t := t) Y
  refine A.finite_toSet.subset fun v hv => ?_
  by_contra hvA
  exact hv (max_eq_left (entryNorm_matrixComponent_le_one (hA v hvA)))

omit [NumberField F] in
theorem finprod_le_finprod_of_one_le {f g : FinitePlace F → ℝ} (hf : ∀ v, 1 ≤ f v)
    (hfg : ∀ v, f v ≤ g v) (hg : (Function.mulSupport g).Finite) :
    ∏ᶠ v, f v ≤ ∏ᶠ v, g v := by
  have hsub : Function.mulSupport f ⊆ Function.mulSupport g := by
    intro v hv
    have h1 : 1 < f v := lt_of_le_of_ne (hf v) (Ne.symm hv)
    exact ne_of_gt (h1.trans_le (hfg v))
  rw [finprod_eq_prod_of_mulSupport_subset f (s := hg.toFinset)
      (by rw [Set.Finite.coe_toFinset]; exact hsub),
    finprod_eq_prod_of_mulSupport_subset g (s := hg.toFinset)
      (by rw [Set.Finite.coe_toFinset])]
  exact Finset.prod_le_prod₀ (fun v _ => zero_le_one.trans (hf v)) fun v _ => hfg v

omit [NumberField F] in
theorem finprod_rpow_of_one_le {f : FinitePlace F → ℝ} (hf : ∀ v, 1 ≤ f v)
    (hfin : (Function.mulSupport f).Finite) (e : ℝ) :
    (∏ᶠ v, f v) ^ e = ∏ᶠ v, f v ^ e := by
  have hsub : Function.mulSupport (fun v => f v ^ e) ⊆ Function.mulSupport f := by
    intro v hv h
    apply hv
    change f v ^ e = 1
    rw [h, Real.one_rpow]
  rw [finprod_eq_prod_of_mulSupport_subset f (s := hfin.toFinset)
      (by rw [Set.Finite.coe_toFinset]),
    finprod_eq_prod_of_mulSupport_subset (fun v => f v ^ e) (s := hfin.toFinset)
      (by rw [Set.Finite.coe_toFinset]; exact hsub)]
  exact (Real.finsetProd_rpow _ _ (fun v _ => zero_le_one.trans (hf v)) e).symm

omit [NumberField F] in
theorem one_le_finprod_of_one_le {f : FinitePlace F → ℝ} (hf : ∀ v, 1 ≤ f v)
    (hfin : (Function.mulSupport f).Finite) : 1 ≤ ∏ᶠ v, f v := by
  rw [finprod_eq_prod_of_mulSupport_subset f (s := hfin.toFinset)
    (by rw [Set.Finite.coe_toFinset])]
  exact Finset.one_le_prod₀ fun v _ => hf v

/-- The archimedean product `∏_v max(1, ‖Y_v‖)^(m_v)` controls the archimedean weight: for
`e ≥ 0`, `(∏_v max(1, ‖Y_v‖)^(m_v))^(-e) ≤ 2^e (1 + ‖Y_∞‖)^(-e)`. -/
theorem prod_rpow_neg_le_archWeight (Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F))
    {e : ℝ} (he : 0 ≤ e) :
    (∏ v : InfinitePlace F, (max 1 (archEntryNorm v Y)) ^ v.mult) ^ (-e) ≤
      2 ^ e * archWeight e Y := by
  set hI : InfinitePlace F → ℝ := fun v => max 1 (archEntryNorm v Y) with hIdef
  obtain ⟨v₀, -, hv₀⟩ := Finset.exists_max_image Finset.univ hI Finset.univ_nonempty
  have hB : 0 ≤ hI v₀ := zero_le_one.trans (le_max_left _ _)
  have hloc : ∀ w : InfinitePlace F, ∀ i j,
      ‖infiniteProjection F w (Y i j)‖ ≤ hI v₀ := fun w i j =>
    (norm_le_archEntryNorm w Y i j).trans ((le_max_right _ _).trans (hv₀ w (Finset.mem_univ _)))
  have hnorm : ‖(matrixSplit F (t + 1) (r + 1) Y).1‖ ≤ hI v₀ := by
    refine (pi_norm_le_iff_of_nonneg hB).2 fun q => ?_
    change ‖InfiniteAdeleRing.ringEquiv_mixedSpace F
      (Y (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2).1‖ ≤ _
    rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, norm_prod_le_iff]
    constructor
    · refine (pi_norm_le_iff_of_nonneg hB).2 fun w => ?_
      rw [(isometry_extensionEmbeddingOfIsReal w.2).norm_map_of_map_zero (map_zero _)]
      exact hloc w.1 _ _
    · refine (pi_norm_le_iff_of_nonneg hB).2 fun w => ?_
      rw [(isometry_extensionEmbedding w.1).norm_map_of_map_zero (map_zero _)]
      exact hloc w.1 _ _
  have h1 : hI v₀ ≤ ∏ v, hI v ^ v.mult := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v₀)]
    have hpow : hI v₀ ≤ hI v₀ ^ v₀.mult := le_self_pow₀ (le_max_left _ _) InfinitePlace.mult_pos.ne'
    calc hI v₀ ≤ hI v₀ ^ v₀.mult * 1 := by rw [mul_one]; exact hpow
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (Finset.one_le_prod₀ fun v _ => one_le_pow₀ (le_max_left _ _)) (pow_nonneg hB _)
  have h2 : (1 + ‖(matrixSplit F (t + 1) (r + 1) Y).1‖) / 2 ≤ ∏ v, hI v ^ v.mult := by
    have := le_max_left 1 (archEntryNorm v₀ Y)
    linarith
  have hpos : 0 < (1 + ‖(matrixSplit F (t + 1) (r + 1) Y).1‖) / 2 := by positivity
  calc (∏ v, hI v ^ v.mult) ^ (-e)
      ≤ ((1 + ‖(matrixSplit F (t + 1) (r + 1) Y).1‖) / 2) ^ (-e) :=
        Real.rpow_le_rpow_of_nonpos hpos h2 (neg_nonpos.mpr he)
    _ = 2 ^ e * archWeight e Y := by
        rw [archWeight_eq, Real.div_rpow (by positivity) zero_le_two, Real.rpow_neg zero_le_two,
          div_inv_eq_mul, mul_comm]

/-- **The determinant bound on the open cell.** If `w u'(Y) = p k` with `k` in the standard
maximal compact subgroup and `m₂` is the second diagonal block of `p`, then for `e ≥ 0`
`|det m₂|_𝔸^(-e) ≤ ((t + 2)!^d)^e 2^e Ω_e(Y)`, `d = [F : ℚ]`. -/
theorem rpow_neg_absDet_le_majorant {p : Full F (blockShape r t)} {k : AdelicGL F (r + t + 2)}
    {Y : Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)}
    (hk : k ∈ standardCompact F (r + t + 2))
    (hpk : p.val * k = openCellWeyl F r t * openCellUnipotent F r t Y) {e : ℝ} (he : 0 ≤ e) :
    absDet F (t + 1) (Oneplace.leviSnd ((blockShape r t).leviProjection (Adeles F) p)) ^ (-e) ≤
      (((t + 2).factorial : ℝ) ^ Module.finrank ℚ F) ^ e * 2 ^ e * majorant e Y := by
  set m₂ := Oneplace.leviSnd ((blockShape r t).leviProjection (Adeles F) p)
  set C : ℝ := ((t + 2).factorial : ℝ) with hCdef
  set hI : InfinitePlace F → ℝ := fun v => max 1 (archEntryNorm v Y)
  set hF : FinitePlace F → ℝ := fun v => max 1 (entryNorm (matrixComponent v Y))
  set dI : InfinitePlace F → ℝ := fun v => ‖(m₂.val.map (infiniteProjection F v)).det‖
  set dF : FinitePlace F → ℝ := fun v => ‖(m₂.val.map (finiteProjection F v)).det‖
  have hX : absDet F (t + 1) m₂ = (∏ v, dI v ^ v.mult) * ∏ᶠ v, dF v := absDet_eq_prod m₂
  have hCpos : 0 < C := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hI1 : ∀ v, 1 ≤ hI v := fun v => le_max_left _ _
  have hF1 : ∀ v, 1 ≤ hF v := fun v => le_max_left _ _
  have hHI : ∏ v, hI v ^ v.mult ≤ C ^ Module.finrank ℚ F * ∏ v, dI v ^ v.mult := by
    calc ∏ v, hI v ^ v.mult ≤ ∏ v, (C * dI v) ^ v.mult :=
          Finset.prod_le_prod₀ (fun v _ => pow_nonneg (zero_le_one.trans (hI1 v)) _)
            fun v _ => pow_le_pow_left₀ (zero_le_one.trans (hI1 v))
              (max_one_archEntryNorm_le_norm_det v hk hpk) _
      _ = C ^ Module.finrank ℚ F * ∏ v, dI v ^ v.mult := by
          simp_rw [mul_pow]
          rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
  have hHF : ∏ᶠ v, hF v ≤ ∏ᶠ v, dF v :=
    finprod_le_finprod_of_one_le hF1 (fun v => max_one_entryNorm_le_norm_det v hk hpk)
      (mulSupport_norm_det_finite m₂)
  have hFfin := mulSupport_max_one_entryNorm_finite (r := r) (t := t) Y
  have hHI1 : 1 ≤ ∏ v, hI v ^ v.mult := Finset.one_le_prod₀ fun v _ => one_le_pow₀ (hI1 v)
  have hHF1 : 1 ≤ ∏ᶠ v, hF v := one_le_finprod_of_one_le hF1 hFfin
  set HI := ∏ v, hI v ^ v.mult with hHIdef
  set HF := ∏ᶠ v, hF v with hHFdef
  set D := C ^ Module.finrank ℚ F with hDdef
  have hlow : HI * HF ≤ D * absDet F (t + 1) m₂ := by
    rw [hX, ← mul_assoc]
    exact mul_le_mul hHI hHF (zero_le_one.trans hHF1)
      (mul_nonneg (pow_nonneg hCpos.le _) (Finset.prod_nonneg fun v _ => by positivity))
  have hCd : 0 < D := pow_pos hCpos _
  have hprodpos : 0 < HI * HF := by positivity
  have hstep : absDet F (t + 1) m₂ ^ (-e) ≤ ((HI * HF) / D) ^ (-e) := by
    refine Real.rpow_le_rpow_of_nonpos (div_pos hprodpos hCd) ?_ (neg_nonpos.mpr he)
    rw [div_le_iff₀ hCd, mul_comm (absDet F (t + 1) m₂) D]
    exact hlow
  have hsplit : ((HI * HF) / D) ^ (-e) = D ^ e * (HI ^ (-e) * HF ^ (-e)) := by
    rw [Real.div_rpow hprodpos.le hCd.le, Real.mul_rpow (by positivity) (by positivity),
      Real.rpow_neg hCd.le, div_inv_eq_mul, mul_comm]
  have hfin : HF ^ (-e) = finiteWeight e Y :=
    finprod_rpow_of_one_le hF1 hFfin (-e)
  refine hstep.trans (le_of_eq_of_le hsplit ?_)
  rw [hfin, majorant]
  calc D ^ e * (HI ^ (-e) * finiteWeight e Y)
      ≤ D ^ e * ((2 ^ e * archWeight e Y) * finiteWeight e Y) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (prod_rpow_neg_le_archWeight Y he) (finiteWeight_pos e Y).le)
          (Real.rpow_nonneg hCd.le _)
    _ = D ^ e * 2 ^ e * (archWeight e Y * finiteWeight e Y) := by ring

end Global

end Langlands.Global.CuspidalPairEisenstein.OpenCellDeterminant
