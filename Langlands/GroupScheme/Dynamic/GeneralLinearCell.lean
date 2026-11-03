import Langlands.GroupScheme.Dynamic.GeneralLinear

/-! # The opposite open cell of `GL_n` for a weight vector: matrix algebra

For weights `e : n → ℤ`, an invertible matrix `g` over a commutative ring is a product `u p` of
a matrix `u` in the block unipotent subgroup for `-e` and a matrix `p` in the block parabolic
subgroup for `e` as soon as the cell minor `δ_e(g)`, the product of the determinants of the
upper threshold blocks `{l | c ≤ e l}`, is a unit. Conversely `δ_e(u p)` is a unit, and the two
subgroups meet trivially.
-/

noncomputable section

open Matrix

namespace Langlands.GroupScheme.GeneralLinear

variable {n : Type} [Fintype n] [DecidableEq n] {A : Type*} [CommRing A] (e : n → ℤ)

section Blocks

/-- The square block of `M` on the upper threshold set `{l | c ≤ e l}`. -/
def thresholdBlock (c : ℤ) (M : Matrix n n A) : Matrix {l // c ≤ e l} {l // c ≤ e l} A :=
  M.toSquareBlockProp fun l => c ≤ e l

/-- The columns of `M` indexed by the upper threshold set `{l | c ≤ e l}`. -/
def thresholdColumns (c : ℤ) (M : Matrix n n A) : Matrix n {l // c ≤ e l} A :=
  M.submatrix id Subtype.val

/-- The cell minor `δ_e(M)`: the product, over the values `c` of `e`, of the determinants of the
upper threshold blocks of `M`. -/
def cellMinor (M : Matrix n n A) : A :=
  ∏ c ∈ Finset.univ.image e, (thresholdBlock e c M).det

theorem map_cellMinor {B : Type*} [CommRing B] (f : A →+* B) (M : Matrix n n A) :
    f (cellMinor e M) = cellMinor e (M.map f) := by
  rw [cellMinor, cellMinor, map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [RingHom.map_det]
  rfl

theorem isUnit_thresholdBlock_of_isUnit_cellMinor {M : Matrix n n A}
    (h : IsUnit (cellMinor e M)) (j : n) : IsUnit (thresholdBlock e (e j) M).det :=
  IsUnit.prod_iff.1 h (e j) (Finset.mem_image_of_mem e (Finset.mem_univ j))

omit [DecidableEq n] in
/-- The threshold block of a product is the product of the threshold blocks when the left factor
has no entries from the threshold rows to the other columns. -/
theorem thresholdBlock_mul_of_left (c : ℤ) {X Y : Matrix n n A}
    (hX : ∀ i m, c ≤ e i → e m < c → X i m = 0) :
    thresholdBlock e c (X * Y) = thresholdBlock e c X * thresholdBlock e c Y := by
  ext i j
  simp only [thresholdBlock, toSquareBlockProp_def, of_apply, mul_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun l => c ≤ e l)]
  have h0 : ∑ m : {l // ¬c ≤ e l}, X i m * Y m j = 0 :=
    Finset.sum_eq_zero fun m _ => by rw [hX i m i.2 (not_le.1 m.2), zero_mul]
  rw [h0, add_zero]

omit [DecidableEq n] in
/-- The threshold block of a product is the product of the threshold blocks when the right factor
has no entries from the other rows to the threshold columns. -/
theorem thresholdBlock_mul_of_right (c : ℤ) {X Y : Matrix n n A}
    (hY : ∀ m j, e m < c → c ≤ e j → Y m j = 0) :
    thresholdBlock e c (X * Y) = thresholdBlock e c X * thresholdBlock e c Y := by
  ext i j
  simp only [thresholdBlock, toSquareBlockProp_def, of_apply, mul_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun l => c ≤ e l)]
  have h0 : ∑ m : {l // ¬c ≤ e l}, X i m * Y m j = 0 :=
    Finset.sum_eq_zero fun m _ => by rw [hY m j (not_le.1 m.2) j.2, mul_zero]
  rw [h0, add_zero]

omit [Fintype n] in
theorem thresholdBlock_one (c : ℤ) : thresholdBlock e c (1 : Matrix n n A) = 1 := by
  ext i j
  simp only [thresholdBlock, toSquareBlockProp_def, of_apply, one_apply, Subtype.ext_iff]

/-- Threshold blocks of block unipotent matrices for `-e` are invertible. -/
theorem isUnit_det_thresholdBlock_of_unipotent (c : ℤ) {u : GL n A}
    (hu : u ∈ blockUnipotentSubgroup A (-e)) :
    IsUnit (thresholdBlock e c (u : Matrix n n A)).det := by
  have hX : ∀ (v : GL n A), v ∈ blockUnipotentSubgroup A (-e) →
      ∀ i m, c ≤ e i → e m < c → (v : Matrix n n A) i m = 0 := by
    intro v hv i m hi hm
    rw [hv i m (by simp only [Pi.neg_apply]; omega)]
    exact one_apply_ne fun h => by subst h; omega
  have h := thresholdBlock_mul_of_left e c (Y := ((u⁻¹ : GL n A) : Matrix n n A)) (hX u hu)
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, thresholdBlock_one] at h
  exact IsUnit.of_mul_eq_one (thresholdBlock e c ((u⁻¹ : GL n A) : Matrix n n A)).det
    (by rw [← det_mul, ← h, det_one])

/-- Threshold blocks of block parabolic matrices for `e` are invertible. -/
theorem isUnit_det_thresholdBlock_of_parabolic (c : ℤ) {p : GL n A}
    (hp : p ∈ blockParabolicSubgroup A e) :
    IsUnit (thresholdBlock e c (p : Matrix n n A)).det := by
  have hY : ∀ (q : GL n A), q ∈ blockParabolicSubgroup A e →
      ∀ m j, e m < c → c ≤ e j → (q : Matrix n n A) m j = 0 :=
    fun q hq m j hm hj => (mem_blockParabolicSubgroup A e).1 hq m j (by omega)
  have h := thresholdBlock_mul_of_right e c (X := ((p⁻¹ : GL n A) : Matrix n n A)) (hY p hp)
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one, thresholdBlock_one] at h
  exact IsUnit.of_mul_eq_one_right (thresholdBlock e c ((p⁻¹ : GL n A) : Matrix n n A)).det
    (by rw [← det_mul, ← h, det_one])

/-- The cell minor of a product `u p` with `u` block unipotent for `-e` and `p` block parabolic
for `e` is a unit. -/
theorem isUnit_cellMinor_mul {u p : GL n A} (hu : u ∈ blockUnipotentSubgroup A (-e))
    (hp : p ∈ blockParabolicSubgroup A e) :
    IsUnit (cellMinor e ((u * p : GL n A) : Matrix n n A)) := by
  refine IsUnit.prod_iff.2 fun c _ => ?_
  rw [Units.val_mul, thresholdBlock_mul_of_right e c (fun m j hm hj => (mem_blockParabolicSubgroup A e).1 hp m j (by omega)),
    det_mul]
  exact (isUnit_det_thresholdBlock_of_unipotent e c hu).mul
    (isUnit_det_thresholdBlock_of_parabolic e c hp)

/-- The block unipotent subgroup for `-e` and the block parabolic subgroup for `e` meet
trivially. -/
theorem blockUnipotentSubgroup_neg_inf_blockParabolicSubgroup :
    blockUnipotentSubgroup A (-e) ⊓ blockParabolicSubgroup A e = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  obtain ⟨hU, hP⟩ := Subgroup.mem_inf.1 hx
  refine Units.ext (Matrix.ext fun i j => ?_)
  rcases le_or_gt (e j) (e i) with h | h
  · exact hU i j (by simp only [Pi.neg_apply]; omega)
  · rw [(mem_blockParabolicSubgroup A e).1 hP i j h, Units.val_one]
    exact (one_apply_ne fun hij => by subst hij; omega).symm

end Blocks

section Decomposition

variable {M : Matrix n n A}

/-- The matrix `M_{:,S_c} (M_{S_c S_c})⁻¹` for the upper threshold set `S_c = {l | c ≤ e l}`. -/
def cellRatio (c : ℤ) (M : Matrix n n A) : Matrix n {l // c ≤ e l} A :=
  thresholdColumns e c M * (thresholdBlock e c M)⁻¹

/-- The unipotent factor of the cell decomposition: its column `j` is column `j` of
`cellRatio e (e j) M`. -/
def cellLower (M : Matrix n n A) : Matrix n n A :=
  Matrix.of fun i j => cellRatio e (e j) M i ⟨j, le_rfl⟩

theorem thresholdColumns_eq_cellRatio_mul {c : ℤ} (hc : IsUnit (thresholdBlock e c M).det) :
    thresholdColumns e c M = cellRatio e c M * thresholdBlock e c M := by
  rw [cellRatio, Matrix.mul_assoc, nonsing_inv_mul _ hc, Matrix.mul_one]

theorem cellRatio_of_le {c : ℤ} (hc : IsUnit (thresholdBlock e c M).det) {i : n} (hi : c ≤ e i)
    (m : {l // c ≤ e l}) :
    cellRatio e c M i m = (1 : Matrix {l // c ≤ e l} {l // c ≤ e l} A) ⟨i, hi⟩ m := by
  rw [← mul_nonsing_inv _ hc]
  rfl

/-- For `c ≤ c'`, `cellRatio e c'` is `cellRatio e c` times the rows `S_c` of `cellRatio e c'`. -/
theorem cellRatio_eq_mul {c c' : ℤ} (hcc' : c ≤ c') (hc : IsUnit (thresholdBlock e c M).det) :
    cellRatio e c' M = cellRatio e c M * (cellRatio e c' M).submatrix Subtype.val id := by
  have hcols : thresholdColumns e c' M =
      cellRatio e c M * M.submatrix (Subtype.val : {l // c ≤ e l} → n) Subtype.val := by
    have h := congrArg (fun X : Matrix n {l // c ≤ e l} A =>
      X.submatrix id (fun l : {l // c' ≤ e l} => (⟨l.1, hcc'.trans l.2⟩ : {l // c ≤ e l})))
      (thresholdColumns_eq_cellRatio_mul e hc)
    rw [submatrix_mul _ _ _ id _ Function.bijective_id, submatrix_id_id] at h
    exact h
  have hrows : (cellRatio e c' M).submatrix (Subtype.val : {l // c ≤ e l} → n) id =
      M.submatrix (Subtype.val : {l // c ≤ e l} → n) Subtype.val *
        (thresholdBlock e c' M)⁻¹ := by
    rw [cellRatio, submatrix_mul _ _ _ id _ Function.bijective_id, submatrix_id_id]
    rfl
  rw [hrows, ← Matrix.mul_assoc, ← hcols]
  rfl

theorem cellLower_of_le (h : ∀ j, IsUnit (thresholdBlock e (e j) M).det) {i j : n}
    (hij : e j ≤ e i) : cellLower e M i j = (1 : Matrix n n A) i j := by
  change cellRatio e (e j) M i ⟨j, le_rfl⟩ = _
  rw [cellRatio_of_le e (h j) hij, one_apply, one_apply]
  simp only [Subtype.mk.injEq]

theorem det_cellLower (h : ∀ j, IsUnit (thresholdBlock e (e j) M).det) :
    (cellLower e M).det = 1 := by
  have hB : (cellLower e M).BlockTriangular e := fun i j hij => by
    rw [cellLower_of_le e h hij.le]
    exact one_apply_ne fun h' => by subst h'; exact lt_irrefl _ hij
  rw [hB.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have h1 : (cellLower e M).toSquareBlock e a = 1 := by
    ext i j
    rw [toSquareBlock_def, of_apply, cellLower_of_le e h (by rw [i.2, j.2])]
    simp [one_apply, Subtype.ext_iff]
  rw [h1, det_one]

/-- Columns `S_c` of the unipotent factor are `cellRatio e c M` times its block on `S_c`. -/
theorem cellLower_columns {c : ℤ}
    (hc : IsUnit (thresholdBlock e c M).det) :
    thresholdColumns e c (cellLower e M) = cellRatio e c M * thresholdBlock e c (cellLower e M) := by
  ext i l
  have h1 := congrFun (congrFun (cellRatio_eq_mul e (M := M) l.2 hc) i) ⟨l.1, le_rfl⟩
  change cellRatio e (e l.1) M i ⟨l.1, le_rfl⟩ = _
  rw [h1, mul_apply, mul_apply]
  rfl

/-- The unipotent factor of the cell decomposition, as an invertible matrix. -/
def cellLowerUnit (h : ∀ j, IsUnit (thresholdBlock e (e j) M).det) : GL n A :=
  nonsingInvUnit (cellLower e M) (by rw [det_cellLower e h]; exact isUnit_one)

theorem coe_cellLowerUnit (h : ∀ j, IsUnit (thresholdBlock e (e j) M).det) :
    (cellLowerUnit e h : Matrix n n A) = cellLower e M :=
  rfl

theorem cellLowerUnit_mem (h : ∀ j, IsUnit (thresholdBlock e (e j) M).det) :
    cellLowerUnit e h ∈ blockUnipotentSubgroup A (-e) := fun i j hij => by
  rw [coe_cellLowerUnit, cellLower_of_le e h (by simp only [Pi.neg_apply] at hij; omega)]

/-- **Cell decomposition in `GL_n`.** If the cell minor of `g` is a unit, then `g = u p` with `u`
block unipotent for `-e` and `p` block parabolic for `e`. -/
theorem exists_cell_decomposition (g : GL n A) (hg : IsUnit (cellMinor e (g : Matrix n n A))) :
    ∃ u ∈ blockUnipotentSubgroup A (-e), ∃ p ∈ blockParabolicSubgroup A e, g = u * p := by
  have h := isUnit_thresholdBlock_of_isUnit_cellMinor e hg
  have hu := cellLowerUnit_mem e h
  refine ⟨cellLowerUnit e h, hu, (cellLowerUnit e h)⁻¹ * g,
    (mem_blockParabolicSubgroup A e).2 fun i j hij => ?_, by rw [mul_inv_cancel_left]⟩
  have hc := h j
  have huc := isUnit_det_thresholdBlock_of_unipotent e (e j) hu
  -- `u⁻¹ * cellRatio * u_c` is the column block `1_{:,S}`.
  have h3 : (((cellLowerUnit e h)⁻¹ : GL n A) : Matrix n n A) *
      (cellRatio e (e j) (g : Matrix n n A) *
        thresholdBlock e (e j) ((cellLowerUnit e h : GL n A) : Matrix n n A)) =
      thresholdColumns e (e j) (1 : Matrix n n A) := by
    rw [coe_cellLowerUnit, ← cellLower_columns e hc, ← coe_cellLowerUnit e h]
    change _ * ((cellLowerUnit e h : GL n A) : Matrix n n A).submatrix id Subtype.val =
      (1 : Matrix n n A).submatrix id _
    rw [← submatrix_id_id (((cellLowerUnit e h)⁻¹ : GL n A) : Matrix n n A), ← submatrix_mul _ _ _ id _
      Function.bijective_id, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hi : ¬ e j ≤ e i := not_le.2 hij
  have h4 : (((cellLowerUnit e h)⁻¹ : GL n A) : Matrix n n A) * cellRatio e (e j) (g : Matrix n n A) =
      thresholdColumns e (e j) (1 : Matrix n n A) *
        (thresholdBlock e (e j) ((cellLowerUnit e h : GL n A) : Matrix n n A))⁻¹ := by
    rw [← h3, Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ huc, Matrix.mul_one]
  have hrow : ∀ m : {l // e j ≤ e l}, ((((cellLowerUnit e h)⁻¹ : GL n A) : Matrix n n A) *
      cellRatio e (e j) (g : Matrix n n A)) i m = 0 := by
    intro m
    rw [h4, mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    change (1 : Matrix n n A) i l.1 * _ = 0
    rw [one_apply_ne (fun h' => hi (by rw [h']; exact l.2)), zero_mul]
  have hcol : (((cellLowerUnit e h)⁻¹ * g : GL n A) : Matrix n n A) i j =
      ((((cellLowerUnit e h)⁻¹ : GL n A) : Matrix n n A) *
        thresholdColumns e (e j) (g : Matrix n n A)) i ⟨j, le_rfl⟩ := by
    rw [Units.val_mul]
    rfl
  rw [hcol, thresholdColumns_eq_cellRatio_mul e hc, ← Matrix.mul_assoc, mul_apply]
  exact Finset.sum_eq_zero fun m _ => by rw [hrow m, zero_mul]

end Decomposition

end Langlands.GroupScheme.GeneralLinear
