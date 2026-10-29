import Langlands.Group.GL.MirabolicTailConullProof
import Langlands.Group.GL.LowerBlockLocalizationCoordinates
import Langlands.Group.GL.UpperUnipotent
import Langlands.Group.GL.CompactOpen
import Langlands.Analysis.Local.QuotientCompactOpenOrbitProof

/-!
# The lower big cell `N · B⁻` is conull

For an invertible matrix `g`, write `A_k(g)` for the matrix agreeing with `g`
on the rows and columns of index at least `k` and with the identity elsewhere,
so that `det A_k(g)` is the bottom-right minor of size `m - k`. Then `g = u b`
with `u` upper unipotent and `b` invertible lower triangular exactly when all
these minors are nonzero. The complement of `N · B⁻` is closed and null for
every left Haar measure: it is covered by finitely many pieces, each moved off
itself by an elementary transvection with a small nonzero parameter. A
compatible quotient measure on `N \ G` vanishes on every measurable set whose
preimage is Haar-null, so the cosets not represented by `B⁻` form a null set.
-/

namespace Langlands.GeneralLinear

open MeasureTheory Filter Topology Set Matrix

universe uF

section Corner

variable {K : Type*} [Field K] {m : ℕ}

/-- The matrix agreeing with `M` on the rows and columns of index at least `k`
and with the identity matrix elsewhere. Its determinant is the bottom-right
minor of `M` of size `m - k`. -/
def bottomCornerMatrix (k : ℕ) (M : Matrix (Fin m) (Fin m) K) : Matrix (Fin m) (Fin m) K :=
  Matrix.of fun r c =>
    if k ≤ r.val ∧ k ≤ c.val then M r c else (1 : Matrix (Fin m) (Fin m) K) r c

theorem bottomCornerMatrix_apply (k : ℕ) (M : Matrix (Fin m) (Fin m) K) (r c : Fin m) :
    bottomCornerMatrix k M r c =
      if k ≤ r.val ∧ k ≤ c.val then M r c else (1 : Matrix (Fin m) (Fin m) K) r c :=
  rfl

theorem bottomCornerMatrix_apply_of_le {k : ℕ} {M : Matrix (Fin m) (Fin m) K} {r c : Fin m}
    (hr : k ≤ r.val) (hc : k ≤ c.val) : bottomCornerMatrix k M r c = M r c := by
  rw [bottomCornerMatrix_apply, ite_eq_left ⟨hr, hc⟩]

theorem bottomCornerMatrix_apply_of_lt_right {k : ℕ} {M : Matrix (Fin m) (Fin m) K}
    {r c : Fin m} (hc : c.val < k) :
    bottomCornerMatrix k M r c = (1 : Matrix (Fin m) (Fin m) K) r c := by
  rw [bottomCornerMatrix_apply, ite_eq_right (by omega)]

/-- A row above the threshold is the corresponding row of the identity. -/
theorem bottomCornerMatrix_row_of_lt {k : ℕ} {M : Matrix (Fin m) (Fin m) K} {r : Fin m}
    (hr : r.val < k) : bottomCornerMatrix k M r = (1 : Matrix (Fin m) (Fin m) K) r := by
  funext c
  rw [bottomCornerMatrix_apply, ite_eq_right (by omega)]

theorem bottomCornerMatrix_mul_apply_of_lt {k : ℕ} {M : Matrix (Fin m) (Fin m) K}
    (X : Matrix (Fin m) (Fin m) K) {r : Fin m} (hr : r.val < k) (c : Fin m) :
    (bottomCornerMatrix k M * X) r c = X r c := by
  rw [Matrix.mul_apply, bottomCornerMatrix_row_of_lt hr, ← Matrix.mul_apply, Matrix.one_mul]

/-- The corner construction is multiplicative when the left factor has no
entries in the rows at least `k` and the columns below `k`. -/
theorem bottomCornerMatrix_mul (k : ℕ) (X Y : Matrix (Fin m) (Fin m) K)
    (hX : ∀ r l : Fin m, l.val < k → k ≤ r.val → X r l = 0) :
    bottomCornerMatrix k (X * Y) = bottomCornerMatrix k X * bottomCornerMatrix k Y := by
  ext r c
  by_cases hr : k ≤ r.val
  · rw [Matrix.mul_apply]
    by_cases hc : k ≤ c.val
    · rw [bottomCornerMatrix_apply_of_le hr hc, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases hl : k ≤ l.val
      · rw [bottomCornerMatrix_apply_of_le hr hl, bottomCornerMatrix_apply_of_le hl hc]
      · rw [hX r l (by omega) hr, zero_mul, bottomCornerMatrix_apply_of_lt_right (by omega),
          Matrix.one_apply_ne (Fin.ne_of_val_ne (by omega)), zero_mul]
    · rw [bottomCornerMatrix_apply_of_lt_right (by omega),
        Matrix.one_apply_ne (Fin.ne_of_val_ne (by omega))]
      symm
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases hl : k ≤ l.val
      · rw [bottomCornerMatrix_apply_of_lt_right (r := l) (by omega),
          Matrix.one_apply_ne (Fin.ne_of_val_ne (by omega)), mul_zero]
      · rw [bottomCornerMatrix_apply_of_lt_right (r := r) (by omega),
          Matrix.one_apply_ne (Fin.ne_of_val_ne (by omega)), zero_mul]
  · rw [bottomCornerMatrix_mul_apply_of_lt _ (by omega), bottomCornerMatrix_apply,
      bottomCornerMatrix_apply, ite_eq_right (by omega), ite_eq_right (by omega)]

/-- Every corner matrix of an upper unipotent matrix has determinant one. -/
theorem det_bottomCornerMatrix_of_mem_upperUnipotent (k : ℕ) {u : GeneralLinear m K}
    (hu : u ∈ upperUnipotent m K) : (bottomCornerMatrix k u.val).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · refine Finset.prod_eq_one fun r _ => ?_
    rw [bottomCornerMatrix_apply]
    split_ifs
    · exact hu.2 r
    · exact Matrix.one_apply_eq r
  · intro r c hcr
    rw [bottomCornerMatrix_apply]
    split_ifs
    · exact hu.1 hcr
    · exact Matrix.one_apply_ne (ne_of_gt hcr)

/-- Every corner matrix of an invertible lower triangular matrix is invertible. -/
theorem det_bottomCornerMatrix_ne_zero_of_mem_lowerTriangular (k : ℕ) {b : GeneralLinear m K}
    (hb : b ∈ lowerTriangularSubgroup m K) : (bottomCornerMatrix k b.val).det ≠ 0 := by
  have hdiag : ∀ r, b.val r r ≠ 0 := by
    have hdet := Matrix.GeneralLinearGroup.det_ne_zero b
    rw [Matrix.det_of_isLowerTriangular _ hb] at hdet
    exact fun r => Finset.prod_ne_zero_iff.mp hdet r (Finset.mem_univ r)
  rw [Matrix.det_of_isLowerTriangular]
  · refine Finset.prod_ne_zero_iff.mpr fun r _ => ?_
    rw [bottomCornerMatrix_apply]
    split_ifs
    · exact hdiag r
    · rw [Matrix.one_apply_eq]
      exact one_ne_zero
  · intro r c hrc
    have hrc' : r < c := OrderDual.toDual_lt_toDual.mp hrc
    rw [bottomCornerMatrix_apply]
    split_ifs
    · exact (mem_lowerTriangularSubgroup_iff b).mp hb r c hrc'
    · exact Matrix.one_apply_ne (ne_of_lt hrc')

/-- Elements of `N · B⁻` have all bottom-right minors nonzero. -/
theorem det_bottomCornerMatrix_mul_ne_zero (k : ℕ) {u b : GeneralLinear m K}
    (hu : u ∈ upperUnipotent m K) (hb : b ∈ lowerTriangularSubgroup m K) :
    (bottomCornerMatrix k (u * b).val).det ≠ 0 := by
  rw [Units.val_mul, bottomCornerMatrix_mul k _ _ fun r l hl hr =>
      hu.1 (show l < r from Fin.lt_def.mpr (by omega)),
    Matrix.det_mul, det_bottomCornerMatrix_of_mem_upperUnipotent k hu, one_mul]
  exact det_bottomCornerMatrix_ne_zero_of_mem_lowerTriangular k hb

/-- If all bottom-right minors are nonzero then `g ∈ N · B⁻`. Column `c` of the
lower triangular factor `B` with `g B ∈ N` solves `A_c(g) x = e_c`. -/
theorem exists_upperUnipotent_mul_lowerTriangular (g : GeneralLinear m K)
    (hg : ∀ c : Fin m, (bottomCornerMatrix c.val g.val).det ≠ 0) :
    ∃ u ∈ upperUnipotent m K, ∃ b ∈ lowerTriangularSubgroup m K, u * b = g := by
  classical
  let A : Fin m → Matrix (Fin m) (Fin m) K := fun c => bottomCornerMatrix c.val g.val
  have hinv : ∀ c, A c * (A c)⁻¹ = 1 := fun c =>
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hg c))
  let B : Matrix (Fin m) (Fin m) K := Matrix.of fun r c => (A c)⁻¹ r c
  have hB : ∀ r c : Fin m, r < c → B r c = 0 := by
    intro r c hrc
    have h := congrFun (congrFun (hinv c) r) c
    rw [bottomCornerMatrix_mul_apply_of_lt _ (Fin.lt_def.mp hrc),
      Matrix.one_apply_ne (ne_of_lt hrc)] at h
    exact h
  have hU : ∀ r c : Fin m, c ≤ r → (g.val * B) r c = (1 : Matrix (Fin m) (Fin m) K) r c := by
    intro r c hcr
    rw [← congrFun (congrFun (hinv c) r) c, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : c.val ≤ l.val
    · show g.val r l * (A c)⁻¹ l c = bottomCornerMatrix c.val g.val r l * (A c)⁻¹ l c
      rw [bottomCornerMatrix_apply_of_le (Fin.le_def.mp hcr) hl]
    · rw [hB l c (Fin.lt_def.mpr (by omega)), mul_zero]
      show (0 : K) = bottomCornerMatrix c.val g.val r l * (A c)⁻¹ l c
      rw [bottomCornerMatrix_apply_of_lt_right (by omega),
        Matrix.one_apply_ne (Fin.ne_of_val_ne (by have := Fin.le_def.mp hcr; omega)),
        zero_mul]
  have hUt : (g.val * B).IsUpperTriangular := by
    intro r c hcr
    rw [hU r c (le_of_lt hcr), Matrix.one_apply_ne (ne_of_gt (show c < r from hcr))]
  have hdetU : (g.val * B).det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hUt]
    exact Finset.prod_eq_one fun r _ => by rw [hU r r le_rfl, Matrix.one_apply_eq]
  have hdetB : B.det ≠ 0 := by
    intro h
    rw [Matrix.det_mul, h, mul_zero] at hdetU
    exact zero_ne_one hdetU
  let β : GeneralLinear m K := Matrix.GeneralLinearGroup.mkOfDetNeZero B hdetB
  have hβ : β ∈ lowerTriangularSubgroup m K :=
    (mem_lowerTriangularSubgroup_iff β).mpr fun r c h => hB r c h
  have hgβ : (g * β).val = g.val * B := rfl
  refine ⟨g * β, ⟨?_, fun r => ?_⟩, β⁻¹, inv_mem hβ, by group⟩
  · rw [hgβ]
    exact hUt
  · change (g * β).val r r = 1
    rw [hgβ, hU r r le_rfl, Matrix.one_apply_eq]

/-- `g ∈ N · B⁻` exactly when all bottom-right minors of `g` are nonzero. -/
theorem exists_upperUnipotent_mul_lowerTriangular_iff (g : GeneralLinear m K) :
    (∃ u ∈ upperUnipotent m K, ∃ b ∈ lowerTriangularSubgroup m K, u * b = g) ↔
      ∀ c : Fin m, (bottomCornerMatrix c.val g.val).det ≠ 0 := by
  refine ⟨?_, exists_upperUnipotent_mul_lowerTriangular g⟩
  rintro ⟨u, hu, b, hb, rfl⟩ c
  exact det_bottomCornerMatrix_mul_ne_zero c.val hu hb

/-- The complement of `N · B⁻` is the set where some bottom-right minor vanishes. -/
theorem setOf_not_upperUnipotent_mul_lowerTriangular_eq :
    {g : GeneralLinear m K |
        ¬ ∃ u ∈ upperUnipotent m K, ∃ b ∈ lowerTriangularSubgroup m K, u * b = g} =
      ⋃ c : Fin m, {g | (bottomCornerMatrix c.val g.val).det = 0} := by
  ext g
  simp only [mem_ofPred_eq, mem_iUnion, exists_upperUnipotent_mul_lowerTriangular_iff,
    not_forall, not_not]

/-- At a threshold beyond the last index the corner matrix is the identity. -/
theorem bottomCornerMatrix_eq_one {k : ℕ} (hk : m ≤ k) (M : Matrix (Fin m) (Fin m) K) :
    bottomCornerMatrix k M = 1 := by
  ext r c
  exact congrFun (bottomCornerMatrix_row_of_lt (lt_of_lt_of_le r.isLt hk)) c

/-- The determinant obtained from the corner matrix at threshold `i` by
replacing its row `i` with row `j` of `M`, cut down to the columns of index at
least `i`. -/
def bottomCornerExchange (i j : Fin m) (M : Matrix (Fin m) (Fin m) K) : K :=
  ((bottomCornerMatrix i.val M).updateRow i fun c => if i.val ≤ c.val then M j c else 0).det

/-- Adding `t` times row `j` to row `i` changes the corner minor at threshold
`i` by `t` times the exchange determinant. -/
theorem det_bottomCornerMatrix_transvection_mul (i j : Fin m) (t : K)
    (M : Matrix (Fin m) (Fin m) K) :
    (bottomCornerMatrix i.val (Matrix.transvection i j t * M)).det =
      (bottomCornerMatrix i.val M).det + t * bottomCornerExchange i j M := by
  have h : bottomCornerMatrix i.val (Matrix.transvection i j t * M) =
      (bottomCornerMatrix i.val M).updateRow i
        (bottomCornerMatrix i.val M i + t • fun c => if i.val ≤ c.val then M j c else 0) := by
    ext r c
    rw [Matrix.updateRow_apply]
    by_cases hri : r = i
    · rw [ite_eq_left hri, hri, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hc : i.val ≤ c.val
      · rw [bottomCornerMatrix_apply_of_le le_rfl hc, bottomCornerMatrix_apply_of_le le_rfl hc,
          ite_eq_left hc, Matrix.transvection_mul_apply_same]
      · rw [bottomCornerMatrix_apply_of_lt_right (by omega),
          bottomCornerMatrix_apply_of_lt_right (by omega), ite_eq_right hc, mul_zero, add_zero]
    · rw [ite_eq_right hri, bottomCornerMatrix_apply, bottomCornerMatrix_apply,
        Matrix.transvection_mul_apply_of_ne i j r c hri t M]
  rw [h, Matrix.det_updateRow_add, Matrix.updateRow_eq_self, Matrix.det_updateRow_smul,
    bottomCornerExchange]

/-- If the corner minor at threshold `i` vanishes but the next one does not,
some row `j` above `i` gives a nonzero exchange determinant. -/
theorem exists_bottomCornerExchange_ne_zero {n : ℕ} (g : GeneralLinear (n + 1) K)
    (i : Fin (n + 1)) (h0 : (bottomCornerMatrix i.val g.val).det = 0)
    (h1 : (bottomCornerMatrix (i.val + 1) g.val).det ≠ 0) :
    ∃ j : Fin (n + 1), j < i ∧ bottomCornerExchange i j g.val ≠ 0 := by
  classical
  let A := bottomCornerMatrix i.val g.val
  let w : Fin (n + 1) → K := fun c =>
    (-1) ^ (i.val + c.val) * (A.submatrix i.succAbove c.succAbove).det
  have hlin : ∀ v : Fin (n + 1) → K, (A.updateRow i v).det = ∑ c, v c * w c := by
    intro v
    rw [Matrix.det_succ_row _ i]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.updateRow_self, Matrix.submatrix_updateRow_succAbove]
    ring
  let row : Fin (n + 1) → Fin (n + 1) → K := fun r c =>
    if i.val ≤ c.val then g.val r c else 0
  have hrowA : ∀ r, i ≤ r → row r = A r := by
    intro r hr
    funext c
    have hr' := Fin.le_def.mp hr
    by_cases hc : i.val ≤ c.val
    · simp only [row, ite_eq_left hc, A, bottomCornerMatrix_apply_of_le hr' hc]
    · simp only [row, ite_eq_right hc, A, bottomCornerMatrix_apply_of_lt_right (by omega : c.val < i.val)]
      exact (Matrix.one_apply_ne (Fin.ne_of_val_ne (by omega))).symm
  by_contra hcon
  push Not at hcon
  have hall : ∀ r, ∑ c, row r c * w c = 0 := by
    intro r
    rw [← hlin]
    rcases lt_trichotomy r i with hr | hr | hr
    · exact hcon r hr
    · rw [hr, hrowA i le_rfl, Matrix.updateRow_eq_self]
      exact h0
    · refine Matrix.det_zero_of_row_eq (ne_of_lt hr) ?_
      rw [Matrix.updateRow_self, Matrix.updateRow_ne (ne_of_gt hr), hrowA r (le_of_lt hr)]
  let w' : Fin (n + 1) → K := fun c => if i.val ≤ c.val then w c else 0
  have hmul : g.val *ᵥ w' = 0 := by
    funext r
    rw [Matrix.mulVec, dotProduct, Pi.zero_apply, ← hall r]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : i.val ≤ c.val
    · simp only [w', row, ite_eq_left hc]
    · simp only [w', row, ite_eq_right hc, mul_zero, zero_mul]
  have hw' : w' = 0 := by
    have h := congrArg (fun v => (g⁻¹).val *ᵥ v) hmul
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_zero] at h
    exact h
  have hwi : w i = 0 := by
    have h := congrFun hw' i
    simpa only [w', le_refl, ite_true, Pi.zero_apply] using h
  have hsub : (bottomCornerMatrix (i.val + 1) g.val).submatrix i.succAbove i.succAbove =
      A.submatrix i.succAbove i.succAbove := by
    ext r c
    have hr : (i.succAbove r).val ≠ i.val := fun h => Fin.succAbove_ne i r (Fin.ext h)
    have hc : (i.succAbove c).val ≠ i.val := fun h => Fin.succAbove_ne i c (Fin.ext h)
    simp only [Matrix.submatrix_apply, A, bottomCornerMatrix_apply]
    congr 1
    apply propext
    omega
  have hdet1 : (bottomCornerMatrix (i.val + 1) g.val).det =
      (A.submatrix i.succAbove i.succAbove).det := by
    rw [Matrix.det_succ_row _ i, Finset.sum_eq_single i]
    · rw [bottomCornerMatrix_row_of_lt (by omega), Matrix.one_apply_eq, mul_one, hsub,
        Even.neg_one_pow ⟨i.val, rfl⟩, one_mul]
    · intro c _ hc
      rw [bottomCornerMatrix_row_of_lt (by omega), Matrix.one_apply_ne hc.symm, mul_zero,
        zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  apply h1
  rw [hdet1]
  have : w i = (A.submatrix i.succAbove i.succAbove).det := by
    simp only [w, Even.neg_one_pow ⟨i.val, rfl⟩, one_mul]
  rw [← this, hwi]

end Corner

section Null

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] {m : ℕ}

omit [IsTopologicalRing K] in
theorem continuous_bottomCornerMatrix (k : ℕ) :
    Continuous fun g : GeneralLinear m K => bottomCornerMatrix k g.val := by
  refine continuous_matrix fun r c => ?_
  simp only [bottomCornerMatrix_apply]
  exact continuous_if_const _ (fun _ => Units.continuous_val.matrix_elem r c)
    fun _ => continuous_const

theorem continuous_det_bottomCornerMatrix (k : ℕ) :
    Continuous fun g : GeneralLinear m K => (bottomCornerMatrix k g.val).det :=
  (continuous_bottomCornerMatrix k).matrix_det

theorem continuous_bottomCornerExchange (i j : Fin m) :
    Continuous fun g : GeneralLinear m K => bottomCornerExchange i j g.val := by
  unfold bottomCornerExchange
  refine ((continuous_bottomCornerMatrix i.val).matrix_updateRow i ?_).matrix_det
  refine continuous_pi fun c => ?_
  exact continuous_if_const _ (fun _ => Units.continuous_val.matrix_elem j c)
    fun _ => continuous_const

variable [T2Space K]

/-- The complement of `N · B⁻` is closed. -/
theorem isClosed_setOf_not_upperUnipotent_mul_lowerTriangular :
    IsClosed {g : GeneralLinear m K |
      ¬ ∃ u ∈ upperUnipotent m K, ∃ b ∈ lowerTriangularSubgroup m K, u * b = g} := by
  rw [setOf_not_upperUnipotent_mul_lowerTriangular_eq]
  exact isClosed_iUnion_of_finite fun c =>
    isClosed_eq (continuous_det_bottomCornerMatrix c.val) continuous_const

/-- If every neighbourhood of zero in `K` contains a nonzero element, the
complement of `N · B⁻` is null for every inner regular left Haar measure on
`GL_m(K)`. It is covered by the pieces where the minor at threshold `i`
vanishes and the exchange determinant with a row `j < i` does not; the
transvection `1 + t E_{ij}` with small `t ≠ 0` moves each piece off itself. -/
theorem haar_setOf_not_upperUnipotent_mul_lowerTriangular
    [LocallyCompactSpace (GeneralLinear m K)] [MeasurableSpace (GeneralLinear m K)]
    [BorelSpace (GeneralLinear m K)] (hK : ∀ U ∈ 𝓝 (0 : K), ∃ t ∈ U, t ≠ 0)
    (μ : Measure (GeneralLinear m K)) [μ.IsHaarMeasure] [μ.InnerRegular] :
    μ {g : GeneralLinear m K |
      ¬ ∃ u ∈ upperUnipotent m K, ∃ b ∈ lowerTriangularSubgroup m K, u * b = g} = 0 := by
  cases m with
  | zero =>
    rw [setOf_not_upperUnipotent_mul_lowerTriangular_eq, iUnion_of_empty, measure_empty]
  | succ n =>
    let P : Fin (n + 1) → Fin (n + 1) → Set (GeneralLinear (n + 1) K) := fun i j =>
      {g | (bottomCornerMatrix i.val g.val).det = 0 ∧ bottomCornerExchange i j g.val ≠ 0}
    have hcover : {g : GeneralLinear (n + 1) K | ¬ ∃ u ∈ upperUnipotent (n + 1) K,
        ∃ b ∈ lowerTriangularSubgroup (n + 1) K, u * b = g} ⊆
        ⋃ i, ⋃ j, ⋃ (_ : j < i), P i j := by
      intro g hg
      classical
      rw [setOf_not_upperUnipotent_mul_lowerTriangular_eq, mem_iUnion] at hg
      let S := Finset.univ.filter fun c : Fin (n + 1) =>
        (bottomCornerMatrix c.val g.val).det = 0
      have hS : S.Nonempty := by
        obtain ⟨c, hc⟩ := hg
        exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩⟩
      obtain ⟨i, hiS, himax⟩ : ∃ i ∈ S, ∀ c ∈ S, c ≤ i :=
        ⟨S.max' hS, S.max'_mem hS, fun c hc => S.le_max' c hc⟩
      have h0 : (bottomCornerMatrix i.val g.val).det = 0 := (Finset.mem_filter.mp hiS).2
      have h1 : (bottomCornerMatrix (i.val + 1) g.val).det ≠ 0 := by
        by_cases hlt : i.val + 1 < n + 1
        · intro hzero
          have hmem : (⟨i.val + 1, hlt⟩ : Fin (n + 1)) ∈ S :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzero⟩
          have h2 : i.val + 1 ≤ i.val := Fin.le_def.mp (himax _ hmem)
          omega
        · rw [bottomCornerMatrix_eq_one (by omega), Matrix.det_one]
          exact one_ne_zero
      obtain ⟨j, hji, hj⟩ := exists_bottomCornerExchange_ne_zero g i h0 h1
      simp only [mem_iUnion]
      exact ⟨i, j, hji, h0, hj⟩
    refine measure_mono_null hcover (measure_iUnion_null fun i => measure_iUnion_null fun j =>
      measure_iUnion_null fun hji => ?_)
    have hij : i ≠ j := hji.ne'
    have hmeas : MeasurableSet (P i j) :=
      (isClosed_eq (continuous_det_bottomCornerMatrix i.val) continuous_const).measurableSet.inter
        (isOpen_ne_fun (continuous_bottomCornerExchange i j) continuous_const).measurableSet
    refine haar_null_of_forall_nhds_disjoint_translate μ hmeas fun U hU => ?_
    have hφ : transvectionUnit i j hij ⁻¹' U ∈ 𝓝 (0 : K) :=
      (continuous_transvectionUnit i j hij).continuousAt.preimage_mem_nhds
        (by rwa [transvectionUnit_zero])
    obtain ⟨t, htU, ht0⟩ := hK _ hφ
    refine ⟨_, htU, fun g hg hg' => ?_⟩
    obtain ⟨hg0, hgx⟩ := hg
    have key := det_bottomCornerMatrix_transvection_mul i j t g.val
    have hval : (transvectionUnit i j hij t * g).val = Matrix.transvection i j t * g.val := rfl
    rw [← hval, hg'.1, hg0, zero_add, eq_comm, mul_eq_zero] at key
    exact key.elim ht0 hgx

end Null

end Langlands.GeneralLinear

namespace Langlands.QuotientIntegration

open MeasureTheory Set

set_option linter.overlappingInstances false in
/-- A compatible quotient measure on `H \ G` vanishes on every measurable set
whose preimage in `G` is Haar-null, provided `G` has a compact open subgroup
`K`. Each orbit `H g K` carries the pushforward of the Haar restriction to `K`,
and countably many such orbits cover the quotient. -/
theorem IsCompatible.measure_eq_zero_of_preimage {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] {H : Subgroup G} (hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H] [MeasurableSpace (LeftQuotient H)]
    [BorelSpace (LeftQuotient H)] {μG : Measure G} {μH : Measure H}
    [μG.IsHaarMeasure] [μG.Regular] [μH.IsHaarMeasure] [μH.Regular] [μH.IsMulRightInvariant]
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) {μ : Measure (LeftQuotient H)}
    (hμ : IsCompatible H μG μH μ) {S : Set (LeftQuotient H)} (hS : MeasurableSet S)
    (h0 : μG (leftQuotientMap H ⁻¹' S) = 0) : μ S = 0 := by
  have horbit : ∀ g : G,
      μ (S ∩ (fun k : G => leftQuotientMap H (g * k)) '' (K : Set G)) = 0 := by
    intro g
    obtain ⟨-, -, hrestr⟩ := compactOpenOrbitMeasure H hH μG μH K hK μ hμ g
    have hp : Measurable fun k : G => leftQuotientMap H (g * k) :=
      ((leftQuotient_isOpenQuotientMap H).continuous.comp
        (continuous_const.mul continuous_id)).measurable
    have hle : μG.restrict (K : Set G) ((fun k : G => leftQuotientMap H (g * k)) ⁻¹' S) ≤ 0 :=
      calc μG.restrict (K : Set G) ((fun k : G => leftQuotientMap H (g * k)) ⁻¹' S)
          ≤ μG ((fun k : G => leftQuotientMap H (g * k)) ⁻¹' S) := Measure.restrict_apply_le _ _
        _ = μG ((fun k : G => g * k) ⁻¹' (leftQuotientMap H ⁻¹' S)) := rfl
        _ = 0 := by rw [measure_preimage_mul, h0]
    rw [← Measure.restrict_apply hS, hrestr, Measure.smul_apply, Measure.map_apply hp hS,
      nonpos_iff_eq_zero.mp hle, smul_zero]
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun g : G => {x : G | g⁻¹ * x ∈ (K : Set G)})
    fun g => K.isOpen.preimage (continuous_const.mul continuous_id)
  have hcov : S ⊆ ⋃ g ∈ T, S ∩ (fun k : G => leftQuotientMap H (g * k)) '' (K : Set G) := by
    intro x hx
    obtain ⟨y, rfl⟩ := (leftQuotient_isOpenQuotientMap H).surjective x
    have hy : y ∈ ⋃ g ∈ T, {x : G | g⁻¹ * x ∈ (K : Set G)} := by
      rw [hTU]
      refine mem_iUnion.mpr ⟨y, ?_⟩
      show y⁻¹ * y ∈ (K : Set G)
      rw [inv_mul_cancel]
      exact K.one_mem
    obtain ⟨g, hg, hgy⟩ := mem_iUnion₂.mp hy
    refine mem_iUnion₂.mpr ⟨g, hg, hx, g⁻¹ * y, hgy, ?_⟩
    show leftQuotientMap H (g * (g⁻¹ * y)) = leftQuotientMap H y
    rw [mul_inv_cancel_left]
  exact measure_mono_null hcov ((measure_biUnion_null_iff hTc).mpr fun g _ => horbit g)

end Langlands.QuotientIntegration

namespace Langlands.GeneralLinear

open MeasureTheory Filter Topology Set QuotientIntegration

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- In the supplied topology, the complement of `N · B⁻` in `GL_m(F)` is closed
and null for every left Haar measure. -/
theorem padic_setOf_not_upperUnipotent_mul_lowerTriangular (T : F.TopologicalData) (m : ℕ) :
    letI := T.topology
    letI := borel (GeneralLinear m F.Carrier)
    IsClosed {g : GeneralLinear m F.Carrier | ¬ ∃ u ∈ upperUnipotent m F.Carrier,
        ∃ b ∈ lowerTriangularSubgroup m F.Carrier, u * b = g} ∧
      ∀ μ : Measure (GeneralLinear m F.Carrier), μ.IsHaarMeasure →
        μ {g : GeneralLinear m F.Carrier | ¬ ∃ u ∈ upperUnipotent m F.Carrier,
          ∃ b ∈ lowerTriangularSubgroup m F.Carrier, u * b = g} = 0 := by
  let := T.topology
  let mG : MeasurableSpace (GeneralLinear m F.Carrier) := borel _
  have : BorelSpace (GeneralLinear m F.Carrier) := ⟨rfl⟩
  have := T.fieldT2
  have := T.generalLinearTopologicalGroup m
  have := T.generalLinearLocallyCompactSpace m
  have := T.generalLinearSecondCountableTopology m
  have : IsTopologicalRing F.Carrier := by
    let := T.valuativeRel
    have := T.localField
    infer_instance
  refine ⟨isClosed_setOf_not_upperUnipotent_mul_lowerTriangular, fun μ hμ => ?_⟩
  have := hμ
  have : μ.InnerRegular := inferInstance
  exact haar_setOf_not_upperUnipotent_mul_lowerTriangular
    (padic_exists_ne_zero_mem_nhds_zero T) μ

set_option linter.overlappingInstances false in
/-- For every compatible quotient measure on `N_m \ GL_m(F)`, in the supplied
topology, the cosets with no representative in `B⁻` form a null set. -/
theorem padic_lowerTriangular_leftQuotient_conull (T : F.TopologicalData) (m : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (GeneralLinear m F.Carrier)
    letI : BorelSpace (GeneralLinear m F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent m F.Carrier)
    letI : BorelSpace (upperUnipotent m F.Carrier) := ⟨rfl⟩
    letI := borel (LeftQuotient (upperUnipotent m F.Carrier))
    letI : BorelSpace (LeftQuotient (upperUnipotent m F.Carrier)) := ⟨rfl⟩
    ∀ (μG : Measure (GeneralLinear m F.Carrier)) (μH : Measure (upperUnipotent m F.Carrier))
      [μG.IsHaarMeasure] [μG.Regular] [μH.IsHaarMeasure] [μH.Regular]
      [μH.IsMulRightInvariant] (μ : Measure (LeftQuotient (upperUnipotent m F.Carrier))),
      IsCompatible (upperUnipotent m F.Carrier) μG μH μ →
      μ {q | ∀ b ∈ lowerTriangularSubgroup m F.Carrier,
        (Quotient.mk _ b : LeftQuotient (upperUnipotent m F.Carrier)) ≠ q} = 0 := by
  intro μG μH _ _ _ _ _ μ hμ
  let := T.topology
  let mG : MeasurableSpace (GeneralLinear m F.Carrier) := borel _
  have : BorelSpace (GeneralLinear m F.Carrier) := ⟨rfl⟩
  let mN : MeasurableSpace (upperUnipotent m F.Carrier) := borel _
  have : BorelSpace (upperUnipotent m F.Carrier) := ⟨rfl⟩
  let mQ : MeasurableSpace (LeftQuotient (upperUnipotent m F.Carrier)) := borel _
  have : BorelSpace (LeftQuotient (upperUnipotent m F.Carrier)) := ⟨rfl⟩
  have := T.fieldT2
  have := T.generalLinearTopologicalGroup m
  have := T.generalLinearLocallyCompactSpace m
  have := T.generalLinearSecondCountableTopology m
  let N := upperUnipotent m F.Carrier
  have hpre : leftQuotientMap N ⁻¹'
      {q | ∀ b ∈ lowerTriangularSubgroup m F.Carrier, (Quotient.mk _ b : LeftQuotient N) ≠ q} =
      {g : GeneralLinear m F.Carrier |
        ¬ ∃ u ∈ N, ∃ b ∈ lowerTriangularSubgroup m F.Carrier, u * b = g} := by
    ext g
    simp only [mem_preimage, mem_ofPred_eq, leftQuotientMap_apply]
    constructor
    · rintro h ⟨u, hu, b, hb, rfl⟩
      refine h b hb (Quotient.sound (QuotientGroup.rightRel_apply.mpr ?_))
      rw [mul_inv_cancel_right]
      exact hu
    · intro h b hb hbg
      have hrel := QuotientGroup.rightRel_apply.mp (Quotient.exact hbg)
      exact h ⟨g * b⁻¹, hrel, b, hb, inv_mul_cancel_right g b⟩
  have hnull := (padic_setOf_not_upperUnipotent_mul_lowerTriangular T m).2 μG inferInstance
  have hclosed := (padic_setOf_not_upperUnipotent_mul_lowerTriangular T m).1
  have hS : IsClosed
      {q | ∀ b ∈ lowerTriangularSubgroup m F.Carrier, (Quotient.mk _ b : LeftQuotient N) ≠ q} := by
    rw [← (leftQuotient_isOpenQuotientMap N).isQuotientMap.isCoinducing.isClosed_preimage, hpre]
    exact hclosed
  obtain ⟨K, hKc, -⟩ := T.generalLinearCompactOpen m univ univ_mem
  refine IsCompatible.measure_eq_zero_of_preimage UpperUnipotent.isClosed K hKc hμ
    hS.measurableSet ?_
  rw [hpre]
  exact hnull

end Padic

end Langlands.GeneralLinear
