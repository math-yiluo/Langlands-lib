import Langlands.Representation.Conductor.Congruence
import Langlands.Group.GL.UpperUnipotent
import Langlands.Group.GL.RankMaps
import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# Iwasawa decomposition of `GL_(n+1)` over a valued field
-/

noncomputable section

namespace Langlands.GeneralLinear

open Matrix Langlands.Conductor

universe uF uΓ

variable {F : Type uF} [Field F] {Γ₀ : Type uΓ} [LinearOrderedCommGroupWithZero Γ₀]
variable (v : Valuation F Γ₀)

namespace Iwasawa

/-- A quotient by an element of maximal valuation is integral. -/
theorem div_mem_integer {a b : F} (ha : a ≠ 0) (h : v b ≤ v a) : b / a ∈ v.integer := by
  rw [Valuation.mem_integer_iff, map_div₀]
  exact (div_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff v).mpr ha))).mpr h

/-- Integral invertible matrices in every rank, including rank zero. -/
def integralRange (m : ℕ) : Subgroup (Matrix.GeneralLinearGroup (Fin m) F) :=
  (GeneralLinearGroup.map (n := Fin m) v.integer.subtype).range

theorem integralRange_succ (n : ℕ) : integralRange v (n + 1) = integralSubgroup v.integer n :=
  rfl

/-- An invertible matrix from an explicit two-sided inverse. -/
def ofInverse {m : ℕ} (A B : Matrix (Fin m) (Fin m) F) (hAB : A * B = 1) (hBA : B * A = 1) :
    Matrix.GeneralLinearGroup (Fin m) F :=
  ⟨A, B, hAB, hBA⟩

theorem ofInverse_mem {n : ℕ} (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (hAB : A * B = 1) (hBA : B * A = 1) (hA : ∀ i j, A i j ∈ v.integer)
    (hB : ∀ i j, B i j ∈ v.integer) :
    ofInverse A B hAB hBA ∈ integralSubgroup v.integer n :=
  (mem_integralSubgroup v.integer n _).2 ⟨hA, hB⟩

theorem transvection_mem {m : ℕ} (i j : Fin m) {c : F} (hc : c ∈ v.integer) (a b : Fin m) :
    transvection i j c a b ∈ v.integer := by
  simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  refine add_mem ?_ ?_ <;> split_ifs
  all_goals first | exact one_mem _ | exact zero_mem _ | exact hc

/-! ### Rank inclusion in the last coordinate -/

section RankInclusion

variable {R : Type*} [CommRing R] {m : ℕ}

@[simp] theorem rankInclusion_castSucc_castSucc (g : Langlands.GeneralLinear m R) (i j : Fin m) :
    rankInclusion 1 g i.castSucc j.castSucc = g i j :=
  blockSum_apply_left g 1 i j

@[simp] theorem rankInclusion_castSucc_last (g : Langlands.GeneralLinear m R) (i : Fin m) :
    rankInclusion 1 g i.castSucc (Fin.last m) = 0 :=
  blockSum_apply_left_right g 1 i 0

@[simp] theorem rankInclusion_last_castSucc (g : Langlands.GeneralLinear m R) (j : Fin m) :
    rankInclusion 1 g (Fin.last m) j.castSucc = 0 :=
  blockSum_apply_right_left g 1 0 j

@[simp] theorem rankInclusion_last_last (g : Langlands.GeneralLinear m R) :
    rankInclusion 1 g (Fin.last m) (Fin.last m) = 1 :=
  blockSum_apply_right g 1 0 0

end RankInclusion

theorem rankInclusion_map {m : ℕ} (k : Matrix.GeneralLinearGroup (Fin m) v.integer) :
    rankInclusion 1 (GeneralLinearGroup.map v.integer.subtype k) =
      GeneralLinearGroup.map v.integer.subtype (rankInclusion 1 k) := by
  apply Units.ext
  ext i j
  rw [GeneralLinearGroup.map_apply]
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [GeneralLinearGroup.map_apply]

theorem rankInclusion_mem {m : ℕ} {k : Matrix.GeneralLinearGroup (Fin m) F}
    (hk : k ∈ integralRange v m) : rankInclusion 1 k ∈ integralSubgroup v.integer m := by
  obtain ⟨k, rfl⟩ := hk
  rw [rankInclusion_map]
  exact ⟨_, rfl⟩

/-! ### Column reduction of the last row -/

/-- Integral column operations make the last diagonal entry of maximal valuation in its row. -/
theorem exists_last_dominant {m : ℕ} (g : Matrix.GeneralLinearGroup (Fin (m + 1)) F) :
    ∃ k ∈ integralSubgroup v.integer m, (g * k) (Fin.last m) (Fin.last m) ≠ 0 ∧
      ∀ j, v ((g * k) (Fin.last m) j) ≤ v ((g * k) (Fin.last m) (Fin.last m)) := by
  obtain ⟨j0, -, hj0⟩ := Finset.exists_max_image Finset.univ
    (fun j => v (g (Fin.last m) j)) Finset.univ_nonempty
  have hne : g (Fin.last m) j0 ≠ 0 := by
    intro h0
    apply GeneralLinearGroup.det_ne_zero g
    apply Matrix.det_eq_zero_of_row_eq_zero (Fin.last m)
    intro j
    have hj := hj0 j (Finset.mem_univ j)
    rw [h0, map_zero] at hj
    exact (Valuation.zero_iff v).1 (le_antisymm hj zero_le)
  by_cases hle : v (g (Fin.last m) j0) ≤ v (g (Fin.last m) (Fin.last m))
  · refine ⟨1, one_mem _, ?_, ?_⟩
    · rw [mul_one]
      intro h
      rw [h, map_zero] at hle
      exact hne ((Valuation.zero_iff v).1 (le_antisymm hle zero_le))
    · intro j
      rw [mul_one]
      exact (hj0 j (Finset.mem_univ j)).trans hle
  · replace hle := not_le.1 hle
    have hj0l : j0 ≠ Fin.last m := by
      rintro rfl
      exact lt_irrefl _ hle
    have h1 : transvection j0 (Fin.last m) (1 : F) * transvection j0 (Fin.last m) (-1) = 1 := by
      rw [transvection_mul_transvection_same j0 (Fin.last m) hj0l, add_neg_cancel, transvection_zero]
    have h2 : transvection j0 (Fin.last m) (-1 : F) * transvection j0 (Fin.last m) 1 = 1 := by
      rw [transvection_mul_transvection_same j0 (Fin.last m) hj0l, neg_add_cancel, transvection_zero]
    refine ⟨ofInverse _ _ h1 h2,
      ofInverse_mem v _ _ h1 h2 (transvection_mem v _ _ (one_mem _))
        (transvection_mem v _ _ (neg_mem (one_mem _))), ?_⟩
    have hlast : (g * ofInverse _ _ h1 h2) (Fin.last m) (Fin.last m) =
        g (Fin.last m) (Fin.last m) + g (Fin.last m) j0 := by
      change ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * transvection j0 (Fin.last m) (1 : F))
        (Fin.last m) (Fin.last m) = _
      rw [mul_transvection_apply_same, one_mul]
    have hother : ∀ j, j ≠ Fin.last m →
        (g * ofInverse _ _ h1 h2) (Fin.last m) j = g (Fin.last m) j := by
      intro j hj
      change ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) * transvection j0 (Fin.last m) (1 : F))
        (Fin.last m) j = _
      rw [mul_transvection_apply_of_ne j0 (Fin.last m) (Fin.last m) j hj]
    have hv : v ((g * ofInverse _ _ h1 h2) (Fin.last m) (Fin.last m)) =
        v (g (Fin.last m) j0) := by
      rw [hlast]
      exact Valuation.map_add_eq_of_lt_right v hle
    refine ⟨?_, ?_⟩
    · intro h
      rw [h, map_zero] at hv
      exact hne ((Valuation.zero_iff v).1 hv.symm)
    · intro j
      rw [hv]
      by_cases hj : j = Fin.last m
      · rw [hj, ← hv]
      · rw [hother j hj]
        exact hj0 j (Finset.mem_univ j)

/-- The strictly lower part of the last row, scaled by the last entry. -/
def lastRowClearing {m : ℕ} (c : Fin (m + 1) → F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F :=
  Matrix.of fun i j => if i = Fin.last m ∧ j ≠ Fin.last m then c j else 0

theorem lastRowClearing_mul_self {m : ℕ} (c : Fin (m + 1) → F) :
    lastRowClearing c * lastRowClearing c = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro l _
  simp only [lastRowClearing, Matrix.of_apply]
  split_ifs with h h' <;> simp_all

/-- With a dominant nonzero last entry, integral column operations clear the rest of the
last row. -/
theorem exists_clear_last_row {m : ℕ} (h : Matrix.GeneralLinearGroup (Fin (m + 1)) F)
    (hne : h (Fin.last m) (Fin.last m) ≠ 0)
    (hdom : ∀ j, v (h (Fin.last m) j) ≤ v (h (Fin.last m) (Fin.last m))) :
    ∃ k ∈ integralSubgroup v.integer m,
      (∀ j, j ≠ Fin.last m → (h * k) (Fin.last m) j = 0) ∧
        (h * k) (Fin.last m) (Fin.last m) = h (Fin.last m) (Fin.last m) := by
  set c : Fin (m + 1) → F := fun j => h (Fin.last m) j / h (Fin.last m) (Fin.last m) with hc
  set N := lastRowClearing c with hN
  have hNN := lastRowClearing_mul_self c
  have h1 : (1 - N) * (1 + N) = 1 := by
    rw [sub_mul, mul_add, mul_add, one_mul, one_mul, mul_one, hNN]
    abel
  have h2 : (1 + N) * (1 - N) = 1 := by
    rw [add_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, hNN]
    abel
  have hcO : ∀ j, c j ∈ v.integer := fun j => div_mem_integer v hne (hdom j)
  have hNO : ∀ i j, N i j ∈ v.integer := by
    intro i j
    simp only [hN, lastRowClearing, Matrix.of_apply]
    split_ifs
    · exact hcO j
    · exact zero_mem _
  have hmem : ofInverse _ _ h1 h2 ∈ integralSubgroup v.integer m := by
    refine ofInverse_mem v _ _ h1 h2 ?_ ?_
    · intro i j
      rw [Matrix.sub_apply]
      exact sub_mem (by rw [Matrix.one_apply]; split_ifs <;> simp) (hNO i j)
    · intro i j
      rw [Matrix.add_apply]
      exact add_mem (by rw [Matrix.one_apply]; split_ifs <;> simp) (hNO i j)
  have hentry : ∀ j, (h * ofInverse _ _ h1 h2) (Fin.last m) j =
      h (Fin.last m) j - h (Fin.last m) (Fin.last m) * N (Fin.last m) j := by
    intro j
    change (h.val * (1 - N)) (Fin.last m) j = _
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply, Matrix.mul_apply,
      Finset.sum_eq_single (Fin.last m)]
    · intro l _ hl
      simp [hN, lastRowClearing, hl]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  refine ⟨ofInverse _ _ h1 h2, hmem, ?_, ?_⟩
  · intro j hj
    rw [hentry]
    simp only [hN, lastRowClearing, Matrix.of_apply, hj, ne_eq, not_false_eq_true, and_self,
      ite_true, hc]
    field_simp
    ring
  · rw [hentry]
    simp [hN, lastRowClearing]

/-- Removing the last row and column of a matrix whose last row vanishes off the diagonal
multiplies the determinant by the last diagonal entry. -/
theorem det_eq_last_mul_det_castSucc {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
    (hrow : ∀ j, j ≠ Fin.last m → A (Fin.last m) j = 0) :
    A.det = A (Fin.last m) (Fin.last m) * (A.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.det_succ_row A (Fin.last m), Fintype.sum_eq_single (Fin.last m)]
  · rw [Fin.succAbove_last, Fin.val_last, ← two_mul, pow_mul]
    simp
  · intro j hj
    rw [hrow j hj, mul_zero, zero_mul]

/-- Every invertible matrix becomes upper triangular after right multiplication by an
integral invertible matrix. -/
theorem exists_mul_upperTriangular :
    ∀ (m : ℕ) (g : Matrix.GeneralLinearGroup (Fin m) F),
      ∃ k ∈ integralRange v m, (g * k).val.IsUpperTriangular
  | 0, g => ⟨1, one_mem _, fun i => i.elim0⟩
  | m + 1, g => by
    obtain ⟨k1, hk1, hne, hdom⟩ := exists_last_dominant v g
    obtain ⟨k2, hk2, hrow, hlast⟩ := exists_clear_last_row v (g * k1) hne hdom
    set g' := g * k1 * k2 with hg'
    set A : Matrix (Fin m) (Fin m) F := g'.val.submatrix Fin.castSucc Fin.castSucc with hA
    have hdet := det_eq_last_mul_det_castSucc g'.val hrow
    have hAdet : A.det ≠ 0 := by
      intro h0
      apply GeneralLinearGroup.det_ne_zero g'
      rw [hdet, ← hA, h0, mul_zero]
    obtain ⟨k3, hk3, hup⟩ := exists_mul_upperTriangular m (GeneralLinearGroup.mkOfDetNeZero A hAdet)
    refine ⟨k1 * k2 * rankInclusion 1 k3,
      mul_mem (mul_mem hk1 hk2) (rankInclusion_mem v hk3), ?_⟩
    rw [← mul_assoc, ← mul_assoc, ← hg']
    intro i j hji
    induction j using Fin.lastCases with
    | last => exact absurd hji (not_lt.2 (Fin.le_last i))
    | cast j =>
      change (g'.val * (rankInclusion 1 k3).val) i j.castSucc = 0
      rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
      change (∑ l : Fin m, g' i l.castSucc * rankInclusion 1 k3 l.castSucc j.castSucc) +
        g' i (Fin.last m) * rankInclusion 1 k3 (Fin.last m) j.castSucc = 0
      simp only [rankInclusion_castSucc_castSucc, rankInclusion_last_castSucc, mul_zero,
        add_zero]
      induction i using Fin.lastCases with
      | last =>
        apply Finset.sum_eq_zero
        intro l _
        rw [hrow l.castSucc (Fin.castSucc_lt_last l).ne, zero_mul]
      | cast i =>
        have := hup (Fin.castSucc_lt_castSucc_iff.1 hji)
        exact this

/-- Every invertible matrix is an upper triangular matrix times an integral one. -/
theorem exists_upperTriangular_mul {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    ∃ b : Matrix.GeneralLinearGroup (Fin (n + 1)) F, b.val.IsUpperTriangular ∧
      ∃ k ∈ integralSubgroup v.integer n, g = b * k := by
  obtain ⟨k, hk, hb⟩ := exists_mul_upperTriangular v (n + 1) g
  exact ⟨g * k, hb, k⁻¹, inv_mem hk, by rw [mul_inv_cancel_right]⟩

/-! ### Diagonal matrices and the uniformizer -/

/-- The diagonal invertible matrix with the given unit diagonal entries. -/
def diagonalUnits {m : ℕ} : (Fin m → Fˣ) →* Matrix.GeneralLinearGroup (Fin m) F where
  toFun d := ⟨diagonal fun i => (d i : F), diagonal fun i => ((d i)⁻¹ : Fˣ),
    by simp [diagonal_mul_diagonal], by simp [diagonal_mul_diagonal]⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' d e := by
    apply Units.ext
    simp [diagonal_mul_diagonal]

@[simp] theorem diagonalUnits_val {m : ℕ} (d : Fin m → Fˣ) :
    (diagonalUnits d).val = diagonal fun i => (d i : F) :=
  rfl

/-- `ϖ` is a nonzero element of valuation below one whose integral powers realize the
valuation of every nonzero element. -/
def IsUniformizingElement (ϖ : Fˣ) : Prop :=
  v (ϖ : F) < 1 ∧ ∀ x : F, x ≠ 0 → ∃ m : ℤ, v x = v (ϖ : F) ^ m

/-- The diagonal matrix `diag(ϖ ^ lam 0, …, ϖ ^ lam (m - 1))`. -/
def torus {m : ℕ} (ϖ : Fˣ) (lam : Fin m → ℤ) : Matrix.GeneralLinearGroup (Fin m) F :=
  diagonalUnits fun i => ϖ ^ lam i

theorem torus_val {m : ℕ} (ϖ : Fˣ) (lam : Fin m → ℤ) :
    (torus ϖ lam).val = diagonal fun i => ((ϖ ^ lam i : Fˣ) : F) :=
  rfl

theorem torus_inv_val {m : ℕ} (ϖ : Fˣ) (lam : Fin m → ℤ) :
    (torus ϖ lam)⁻¹.val = diagonal fun i => (((ϖ ^ lam i)⁻¹ : Fˣ) : F) :=
  rfl

/-- A diagonal matrix of valuation-one entries is integral. -/
theorem diagonalUnits_mem {n : ℕ} (d : Fin (n + 1) → Fˣ) (hd : ∀ i, v (d i : F) = 1) :
    diagonalUnits d ∈ integralSubgroup v.integer n := by
  rw [mem_integralSubgroup]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · change diagonal (fun i => (d i : F)) i j ∈ v.integer
    rw [diagonal_apply]
    split_ifs
    · exact (Valuation.mem_integer_iff v _).2 (hd i).le
    · exact zero_mem _
  · change diagonal (fun i => (((d i)⁻¹ : Fˣ) : F)) i j ∈ v.integer
    rw [diagonal_apply]
    split_ifs
    · rw [Valuation.mem_integer_iff, Units.val_inv_eq_inv_val, map_inv₀, hd i, inv_one]
    · exact zero_mem _

/-- Diagonal entries of a product of upper triangular matrices multiply. -/
theorem upperTriangular_mul_apply_self {m : ℕ} {A B : Matrix (Fin m) (Fin m) F}
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (i : Fin m) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Fintype.sum_eq_single i]
  intro j hji
  rcases lt_or_gt_of_ne hji with hji | hij
  · rw [hA hji, zero_mul]
  · rw [hB hij, mul_zero]

/-- An integral upper triangular matrix has diagonal entries of valuation one. -/
theorem valuation_diag_eq_one {n : ℕ} {b : Matrix.GeneralLinearGroup (Fin (n + 1)) F}
    (hb : b ∈ integralSubgroup v.integer n) (hu : b.val.IsUpperTriangular) (i : Fin (n + 1)) :
    v (b i i) = 1 := by
  let := b.invertible
  have hi : (b⁻¹).val.IsUpperTriangular := by
    simpa only [Matrix.GeneralLinearGroup.coe_inv] using
      Matrix.blockTriangular_inv_of_blockTriangular hu
  have h : ((b : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *
      ((b⁻¹ : Matrix.GeneralLinearGroup (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F))
        i i = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
  rw [upperTriangular_mul_apply_self hu hi] at h
  rw [mem_integralSubgroup] at hb
  have h1 : v (b i i) ≤ 1 := (Valuation.mem_integer_iff v _).1 (hb.1 i i)
  have h2 : v ((b⁻¹ : Matrix.GeneralLinearGroup (Fin (n + 1)) F) i i) ≤ 1 :=
    (Valuation.mem_integer_iff v _).1 (hb.2 i i)
  have h3 := congrArg v h
  rw [map_mul, map_one] at h3
  refine le_antisymm h1 (not_lt.1 fun hlt => ?_)
  have := lt_of_le_of_lt (mul_le_of_le_one_right' h2) hlt
  rw [h3] at this
  exact lt_irrefl _ this

/-! ### The decomposition `g = u * ϖ ^ lam * k` -/

variable {v}

/-- Iwasawa decomposition: every invertible matrix is an upper unipotent matrix times a
power of the uniformizer on the diagonal times an integral matrix. -/
theorem exists_iwasawa {n : ℕ} {ϖ : Fˣ} (hϖ : IsUniformizingElement v ϖ)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    ∃ u ∈ upperUnipotent (n + 1) F, ∃ lam : Fin (n + 1) → ℤ,
      ∃ k ∈ integralSubgroup v.integer n, g = u * torus ϖ lam * k := by
  obtain ⟨b, hb, k0, hk0, rfl⟩ := exists_upperTriangular_mul v g
  have hd : ∀ i, b i i ≠ 0 := by
    intro i h0
    apply GeneralLinearGroup.det_ne_zero b
    rw [Matrix.det_of_isUpperTriangular hb]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h0
  choose lam hlam using fun i => hϖ.2 (b i i) (hd i)
  set ε : Fin (n + 1) → Fˣ := fun i => (Units.mk0 (b i i) (hd i)) * (ϖ ^ lam i)⁻¹ with hε
  have hεv : ∀ i, v (ε i : F) = 1 := by
    intro i
    rw [hε, Units.val_mul, Units.val_mk0, map_mul, hlam i, Units.val_inv_eq_inv_val,
      map_inv₀, Units.val_zpow_eq_zpow_val, map_zpow₀, mul_inv_cancel₀]
    exact zpow_ne_zero _ ((Valuation.ne_zero_iff v).2 ϖ.ne_zero)
  have hD : torus ϖ lam * diagonalUnits ε = diagonalUnits fun i => Units.mk0 (b i i) (hd i) := by
    rw [torus, ← map_mul]
    congr 1
    funext i
    simp [hε]
  refine ⟨b * (diagonalUnits fun i => Units.mk0 (b i i) (hd i))⁻¹, ?_, lam,
    diagonalUnits ε * k0, mul_mem (diagonalUnits_mem v ε hεv) hk0, ?_⟩
  · have hval : (b * (diagonalUnits fun i => Units.mk0 (b i i) (hd i))⁻¹).val =
        b.val * diagonal fun i => (b i i)⁻¹ := by
      rw [Units.val_mul, ← map_inv, diagonalUnits_val]
      congr 1
    refine ⟨?_, fun i => ?_⟩
    · rw [hval]
      exact hb.mul (Matrix.blockTriangular_diagonal _)
    · change (b * (diagonalUnits fun i => Units.mk0 (b i i) (hd i))⁻¹).val i i = 1
      rw [hval, Matrix.mul_diagonal, mul_inv_cancel₀ (hd i)]
  · rw [← mul_assoc, mul_assoc _ (torus ϖ lam), hD, inv_mul_cancel_right]

/-! ### Uniqueness -/

theorem torus_inv {m : ℕ} (ϖ : Fˣ) (lam : Fin m → ℤ) :
    (torus ϖ lam)⁻¹ = diagonalUnits fun i => (ϖ ^ lam i)⁻¹ := by
  rw [torus, ← map_inv]
  rfl

/-- Entries of a matrix multiplied by diagonal matrices on both sides. -/
theorem diagonalUnits_mul_mul_apply {m : ℕ} (d e : Fin m → Fˣ)
    (b : Matrix.GeneralLinearGroup (Fin m) F) (i j : Fin m) :
    (diagonalUnits d * b * diagonalUnits e) i j = (d i : F) * b i j * (e j : F) := by
  change ((diagonalUnits d).val * b.val * (diagonalUnits e).val) i j = _
  rw [diagonalUnits_val, diagonalUnits_val, Matrix.mul_diagonal, Matrix.diagonal_mul]

variable (v) in
theorem valuation_pos (ϖ : Fˣ) : 0 < v (ϖ : F) :=
  zero_lt_iff.2 ((Valuation.ne_zero_iff v).2 ϖ.ne_zero)

/-- The exponent `lam` of an Iwasawa decomposition `g = u * ϖ ^ lam * k` is unique. -/
theorem iwasawa_exponent_unique {n : ℕ} {ϖ : Fˣ} (hϖ : IsUniformizingElement v ϖ)
    {u u' k k' : Matrix.GeneralLinearGroup (Fin (n + 1)) F} {lam lam' : Fin (n + 1) → ℤ}
    (hu : u ∈ upperUnipotent (n + 1) F) (hu' : u' ∈ upperUnipotent (n + 1) F)
    (hk : k ∈ integralSubgroup v.integer n) (hk' : k' ∈ integralSubgroup v.integer n)
    (h : u * torus ϖ lam * k = u' * torus ϖ lam' * k') : lam = lam' := by
  have hw : u'⁻¹ * u ∈ upperUnipotent (n + 1) F := mul_mem (inv_mem hu') hu
  have hbK : (torus ϖ lam')⁻¹ * (u'⁻¹ * u) * torus ϖ lam ∈ integralSubgroup v.integer n := by
    have hb : (torus ϖ lam')⁻¹ * (u'⁻¹ * u) * torus ϖ lam = k' * k⁻¹ := by
      calc (torus ϖ lam')⁻¹ * (u'⁻¹ * u) * torus ϖ lam
          = (torus ϖ lam')⁻¹ * u'⁻¹ * (u * torus ϖ lam * k) * k⁻¹ := by group
        _ = (torus ϖ lam')⁻¹ * u'⁻¹ * (u' * torus ϖ lam' * k') * k⁻¹ := by rw [h]
        _ = k' * k⁻¹ := by group
    rw [hb]
    exact mul_mem hk' (inv_mem hk)
  rw [torus_inv] at hbK
  have hbu : ((diagonalUnits fun i => (ϖ ^ lam' i)⁻¹) * (u'⁻¹ * u) *
      torus ϖ lam).val.IsUpperTriangular := by
    rw [Units.val_mul, Units.val_mul, diagonalUnits_val, torus_val]
    exact ((Matrix.blockTriangular_diagonal _).mul hw.1).mul (Matrix.blockTriangular_diagonal _)
  funext i
  have h1 := valuation_diag_eq_one v hbK hbu i
  simp only [torus, diagonalUnits_mul_mul_apply] at h1
  rw [hw.2 i, mul_one, map_mul, Units.val_inv_eq_inv_val, map_inv₀,
    Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, map_zpow₀, map_zpow₀,
    inv_mul_eq_one₀ (zpow_ne_zero _ (valuation_pos v ϖ).ne')] at h1
  exact ((zpow_right_strictAnti₀ (valuation_pos v ϖ) hϖ.1).injective h1).symm

/-- Conjugating an integral matrix by `ϖ ^ lam` for antitone `lam` gives integral entries on
and above the diagonal. -/
theorem torus_conj_entry_mem {n : ℕ} {ϖ : Fˣ} (hϖ : v (ϖ : F) ≤ 1)
    {lam : Fin (n + 1) → ℤ} (hlam : Antitone lam)
    {w b : Matrix.GeneralLinearGroup (Fin (n + 1)) F} (hw : w.val.IsUpperTriangular)
    (hb : ∀ i j, b i j ∈ v.integer) (hwb : w = torus ϖ lam * b * (torus ϖ lam)⁻¹)
    (i j : Fin (n + 1)) : w i j ∈ v.integer := by
  rcases lt_or_ge j i with hji | hij
  · rw [hw hji]
    exact zero_mem _
  · have hne : v (ϖ : F) ^ lam j ≠ 0 := zpow_ne_zero _ (valuation_pos v ϖ).ne'
    rw [hwb, torus_inv, torus, diagonalUnits_mul_mul_apply, Valuation.mem_integer_iff,
      map_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, Units.val_zpow_eq_zpow_val,
      Units.val_zpow_eq_zpow_val, map_zpow₀, map_zpow₀, mul_right_comm, mul_comm,
      ← div_eq_mul_inv, ← zpow_sub₀ (valuation_pos v ϖ).ne']
    exact mul_le_one' ((Valuation.mem_integer_iff v _).1 (hb i j))
      (zpow_le_one₀ (valuation_pos v ϖ) hϖ (sub_nonneg.2 (hlam hij)))

/-- For an antitone exponent, the unipotent parts of two Iwasawa decompositions with the same
exponent differ by an integral matrix. -/
theorem iwasawa_unipotent_ambiguity {n : ℕ} {ϖ : Fˣ} (hϖ : v (ϖ : F) ≤ 1)
    {lam : Fin (n + 1) → ℤ} (hlam : Antitone lam)
    {u u' k k' : Matrix.GeneralLinearGroup (Fin (n + 1)) F}
    (hu : u ∈ upperUnipotent (n + 1) F) (hu' : u' ∈ upperUnipotent (n + 1) F)
    (hk : k ∈ integralSubgroup v.integer n) (hk' : k' ∈ integralSubgroup v.integer n)
    (h : u * torus ϖ lam * k = u' * torus ϖ lam * k') :
    u'⁻¹ * u ∈ integralSubgroup v.integer n := by
  have hw : u'⁻¹ * u ∈ upperUnipotent (n + 1) F := mul_mem (inv_mem hu') hu
  have hconj : u'⁻¹ * u = torus ϖ lam * (k' * k⁻¹) * (torus ϖ lam)⁻¹ := by
    calc u'⁻¹ * u = u'⁻¹ * (u * torus ϖ lam * k) * k⁻¹ * (torus ϖ lam)⁻¹ := by group
      _ = u'⁻¹ * (u' * torus ϖ lam * k') * k⁻¹ * (torus ϖ lam)⁻¹ := by rw [h]
      _ = torus ϖ lam * (k' * k⁻¹) * (torus ϖ lam)⁻¹ := by group
  have hconj' : (u'⁻¹ * u)⁻¹ = torus ϖ lam * (k' * k⁻¹)⁻¹ * (torus ϖ lam)⁻¹ := by
    rw [hconj]
    group
  have hb := (mem_integralSubgroup v.integer n _).1 (mul_mem hk' (inv_mem hk))
  exact (mem_integralSubgroup v.integer n _).2
    ⟨torus_conj_entry_mem hϖ hlam hw.1 hb.1 hconj,
      torus_conj_entry_mem hϖ hlam (inv_mem hw).1 hb.2 hconj'⟩

/-! ### The exponent of an invertible matrix -/

/-- The exponent `lam` of the Iwasawa decomposition `g = u * ϖ ^ lam * k`, unique by
`iwasawa_exponent_unique`. -/
def exponent {n : ℕ} {ϖ : Fˣ} (hϖ : IsUniformizingElement v ϖ)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) : Fin (n + 1) → ℤ :=
  (exists_iwasawa hϖ g).choose_spec.2.choose

theorem exists_eq_exponent {n : ℕ} {ϖ : Fˣ} (hϖ : IsUniformizingElement v ϖ)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    ∃ u ∈ upperUnipotent (n + 1) F, ∃ k ∈ integralSubgroup v.integer n,
      g = u * torus ϖ (exponent hϖ g) * k :=
  ⟨_, (exists_iwasawa hϖ g).choose_spec.1, (exists_iwasawa hϖ g).choose_spec.2.choose_spec⟩

/-- Any Iwasawa decomposition of `g` has exponent `exponent hϖ g`. -/
theorem exponent_eq {n : ℕ} {ϖ : Fˣ} (hϖ : IsUniformizingElement v ϖ)
    {g u k : Matrix.GeneralLinearGroup (Fin (n + 1)) F} {lam : Fin (n + 1) → ℤ}
    (hu : u ∈ upperUnipotent (n + 1) F) (hk : k ∈ integralSubgroup v.integer n)
    (h : g = u * torus ϖ lam * k) : exponent hϖ g = lam := by
  obtain ⟨u', hu', k', hk', h'⟩ := exists_eq_exponent hϖ g
  exact iwasawa_exponent_unique hϖ hu' hu hk' hk (h'.symm.trans h)

theorem exponent_torus {n : ℕ} {ϖ : Fˣ} (hϖ : IsUniformizingElement v ϖ)
    (lam : Fin (n + 1) → ℤ) : exponent hϖ (torus ϖ lam) = lam :=
  exponent_eq hϖ (one_mem _) (one_mem _) (by rw [one_mul, mul_one])

theorem exponent_mul_integral {n : ℕ} {ϖ : Fˣ} (hϖ : IsUniformizingElement v ϖ)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) {k : Matrix.GeneralLinearGroup (Fin (n + 1)) F}
    (hk : k ∈ integralSubgroup v.integer n) : exponent hϖ (g * k) = exponent hϖ g := by
  obtain ⟨u', hu', k', hk', h'⟩ := exists_eq_exponent hϖ g
  exact exponent_eq hϖ hu' (mul_mem hk' hk) (by rw [← mul_assoc, ← h'])

theorem exponent_unipotent_mul {n : ℕ} {ϖ : Fˣ} (hϖ : IsUniformizingElement v ϖ)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) {u : Matrix.GeneralLinearGroup (Fin (n + 1)) F}
    (hu : u ∈ upperUnipotent (n + 1) F) : exponent hϖ (u * g) = exponent hϖ g := by
  obtain ⟨u', hu', k', hk', h'⟩ := exists_eq_exponent hϖ g
  exact exponent_eq hϖ (mul_mem hu hu') hk' (by rw [mul_assoc u u', mul_assoc u, ← h'])

/-! ### Nonarchimedean local fields -/

/-- A nonarchimedean local field has a uniformizing element for its valuation. -/
theorem exists_isUniformizingElement (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    ∃ ϖ : Kˣ, IsUniformizingElement (ValuativeRel.valuation K) ϖ := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (e.symm (WithZero.exp (-1)))
  have hex : e (ValuativeRel.valuation K x) = WithZero.exp (-1) := by
    rw [hx, e.apply_symm_apply]
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero] at hex
    exact WithZero.exp_ne_zero hex.symm
  refine ⟨Units.mk0 x hx0, ?_, fun y hy => ?_⟩
  · rw [Units.val_mk0, ← e.strictMono.lt_iff_lt, hex, map_one, WithZero.exp_lt_one_iff]
    norm_num
  · have hy0 : e (ValuativeRel.valuation K y) ≠ 0 := by
      simpa using hy
    refine ⟨-WithZero.log (e (ValuativeRel.valuation K y)), ?_⟩
    have key : e (ValuativeRel.valuation K y) = e (ValuativeRel.valuation K x ^
        (-WithZero.log (e (ValuativeRel.valuation K y)))) := by
      rw [map_zpow₀, hex, ← WithZero.exp_zsmul, smul_neg, smul_eq_mul, mul_one, neg_neg,
        WithZero.exp_log hy0]
    exact e.injective key

end Iwasawa

end Langlands.GeneralLinear
