import Langlands.Group.GL.LowerBlockQuotientCoordinates

/-!
# Block coordinates on the lower triangular group

The map `(b, x, h) ↦ [[b, 0], [x, h]]` identifies `B⁻_a × M_{d×a} × B⁻_d` with
`B⁻_{a+d}`, homeomorphically for every topological commutative ring. In these
coordinates the product is
`(b, x, h) · (b', x', h') = (b b', x b' + h x', h h')`.
-/

noncomputable section

namespace Langlands.GeneralLinear

open Topology

universe u

variable {R : Type u} [CommRing R] {a d : ℕ}

section Algebra

/-- A lower-block display with lower triangular diagonal blocks is lower triangular. -/
theorem lowerBlockPair_mem_lowerTriangularSubgroup {g : GeneralLinear a R}
    (hg : g ∈ lowerTriangularSubgroup a R) (x : Matrix (Fin d) (Fin a) R)
    (h : lowerTriangularSubgroup d R) :
    lowerBlockPair g x h ∈ lowerTriangularSubgroup (a + d) R := by
  rw [mem_lowerTriangularSubgroup_iff]
  intro i j hij
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      rw [lowerBlockPair_11]
      exact (mem_lowerTriangularSubgroup_iff g).mp hg i j (by rw [Fin.lt_def] at hij ⊢; simp only [Fin.val_castAdd] at hij; omega)
    | right j => exact lowerBlockPair_12 g x h i j
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      exfalso
      rw [Fin.lt_def] at hij
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hij
      omega
    | right j =>
      rw [lowerBlockPair_22]
      exact (mem_lowerTriangularSubgroup_iff h.val).mp h.property i j
        (by rw [Fin.lt_def] at hij ⊢; simp only [Fin.val_natAdd] at hij; omega)

/-- The upper right block of a lower triangular matrix vanishes. -/
theorem lowerTriangular_apply_castAdd_natAdd (k : lowerTriangularSubgroup (a + d) R)
    (i : Fin a) (j : Fin d) : k.val.val (i.castAdd d) (j.natAdd a) = 0 :=
  (mem_lowerTriangularSubgroup_iff k.val).mp k.property _ _ (by
    rw [Fin.lt_def]
    simp only [Fin.val_natAdd, Fin.val_castAdd]
    omega)

/-- Rows of the first block of a product with a lower triangular left factor. -/
theorem lowerTriangular_mul_apply_castAdd (k : lowerTriangularSubgroup (a + d) R)
    (M : Matrix (Fin (a + d)) (Fin (a + d)) R) (i : Fin a) (j : Fin (a + d)) :
    (k.val.val * M) (i.castAdd d) j =
      ∑ l : Fin a, k.val.val (i.castAdd d) (l.castAdd d) * M (l.castAdd d) j := by
  rw [Matrix.mul_apply, Fin.sum_univ_add]
  simp [lowerTriangular_apply_castAdd_natAdd]

/-- Columns of the last block of a product with a lower triangular right factor. -/
theorem mul_lowerTriangular_apply_natAdd (k : lowerTriangularSubgroup (a + d) R)
    (M : Matrix (Fin (a + d)) (Fin (a + d)) R) (i : Fin (a + d)) (j : Fin d) :
    (M * k.val.val) i (j.natAdd a) =
      ∑ l : Fin d, M i (l.natAdd a) * k.val.val (l.natAdd a) (j.natAdd a) := by
  rw [Matrix.mul_apply, Fin.sum_univ_add]
  simp [lowerTriangular_apply_castAdd_natAdd]

/-- The first diagonal block of a lower triangular matrix, as an invertible lower
triangular matrix; its inverse is the first diagonal block of the inverse. -/
def lowerTriangularFirstBlock (k : lowerTriangularSubgroup (a + d) R) :
    lowerTriangularSubgroup a R :=
  ⟨⟨k.val.val.submatrix (Fin.castAdd d) (Fin.castAdd d),
    (k⁻¹).val.val.submatrix (Fin.castAdd d) (Fin.castAdd d), by
      ext i j
      rw [Matrix.mul_apply]
      have h := congrFun (congrFun (congrArg (fun g : GeneralLinear (a + d) R => g.val)
        (mul_inv_cancel k.val)) (i.castAdd d)) (j.castAdd d)
      simp only [Units.val_mul, Units.val_one] at h
      rw [lowerTriangular_mul_apply_castAdd] at h
      simpa [Matrix.one_apply, Fin.castAdd_inj] using h, by
      ext i j
      rw [Matrix.mul_apply]
      have h := congrFun (congrFun (congrArg (fun g : GeneralLinear (a + d) R => g.val)
        (inv_mul_cancel k.val)) (i.castAdd d)) (j.castAdd d)
      simp only [Units.val_mul, Units.val_one] at h
      rw [← Subgroup.coe_inv, lowerTriangular_mul_apply_castAdd] at h
      simpa [Matrix.one_apply, Fin.castAdd_inj] using h⟩, by
    rw [mem_lowerTriangularSubgroup_iff]
    intro i j hij
    exact (mem_lowerTriangularSubgroup_iff k.val).mp k.property _ _ (by rw [Fin.lt_def] at hij ⊢; simp only [Fin.val_castAdd]; omega)⟩

/-- The last diagonal block of a lower triangular matrix, as an invertible lower
triangular matrix; its inverse is the last diagonal block of the inverse. -/
def lowerTriangularLastBlock (k : lowerTriangularSubgroup (a + d) R) :
    lowerTriangularSubgroup d R :=
  ⟨⟨k.val.val.submatrix (Fin.natAdd a) (Fin.natAdd a),
    (k⁻¹).val.val.submatrix (Fin.natAdd a) (Fin.natAdd a), by
      ext i j
      rw [Matrix.mul_apply]
      have h := congrFun (congrFun (congrArg (fun g : GeneralLinear (a + d) R => g.val)
        (mul_inv_cancel k.val)) (i.natAdd a)) (j.natAdd a)
      simp only [Units.val_mul, Units.val_one] at h
      rw [← Subgroup.coe_inv, mul_lowerTriangular_apply_natAdd] at h
      simpa [Matrix.one_apply, Fin.natAdd_inj] using h, by
      ext i j
      rw [Matrix.mul_apply]
      have h := congrFun (congrFun (congrArg (fun g : GeneralLinear (a + d) R => g.val)
        (inv_mul_cancel k.val)) (i.natAdd a)) (j.natAdd a)
      simp only [Units.val_mul, Units.val_one] at h
      rw [mul_lowerTriangular_apply_natAdd] at h
      simpa [Matrix.one_apply, Fin.natAdd_inj] using h⟩, by
    rw [mem_lowerTriangularSubgroup_iff]
    intro i j hij
    exact (mem_lowerTriangularSubgroup_iff k.val).mp k.property _ _ (by rw [Fin.lt_def] at hij ⊢; simp only [Fin.val_natAdd]; omega)⟩

@[simp] theorem lowerTriangularFirstBlock_apply (k : lowerTriangularSubgroup (a + d) R)
    (i j : Fin a) :
    (lowerTriangularFirstBlock k).val.val i j = k.val.val (i.castAdd d) (j.castAdd d) := rfl

@[simp] theorem lowerTriangularLastBlock_apply (k : lowerTriangularSubgroup (a + d) R)
    (i j : Fin d) :
    (lowerTriangularLastBlock k).val.val i j = k.val.val (i.natAdd a) (j.natAdd a) := rfl

/-- The lower left rectangular block of a matrix in `GL_{a+d}`. -/
def lowerTriangularRectangle (k : lowerTriangularSubgroup (a + d) R) :
    Matrix (Fin d) (Fin a) R :=
  k.val.val.submatrix (Fin.natAdd a) (Fin.castAdd d)

/-- Block coordinates `(b, x, h) ↦ [[b, 0], [x, h]]` on the lower triangular group. -/
def lowerTriangularBlockMap (a d : ℕ) (R : Type u) [CommRing R]
    (z : lowerTriangularSubgroup a R × Matrix (Fin d) (Fin a) R × lowerTriangularSubgroup d R) :
    lowerTriangularSubgroup (a + d) R :=
  ⟨lowerBlockPair z.1.val z.2.1 z.2.2,
    lowerBlockPair_mem_lowerTriangularSubgroup z.1.property z.2.1 z.2.2⟩

@[simp] theorem lowerTriangularBlockMap_val (z : lowerTriangularSubgroup a R ×
    Matrix (Fin d) (Fin a) R × lowerTriangularSubgroup d R) :
    (lowerTriangularBlockMap a d R z).val = lowerBlockPair z.1.val z.2.1 z.2.2 := rfl

/-- The block coordinates as an equivalence. -/
def lowerTriangularBlockEquiv (a d : ℕ) (R : Type u) [CommRing R] :
    (lowerTriangularSubgroup a R × Matrix (Fin d) (Fin a) R × lowerTriangularSubgroup d R) ≃
      lowerTriangularSubgroup (a + d) R where
  toFun := lowerTriangularBlockMap a d R
  invFun k := (lowerTriangularFirstBlock k, lowerTriangularRectangle k,
    lowerTriangularLastBlock k)
  left_inv := by
    rintro ⟨b, x, h⟩
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · apply Subtype.ext
      apply Units.ext
      ext i j
      exact lowerBlockPair_11 b.val x h i j
    · ext i j
      exact lowerBlockPair_21 b.val x h i j
    · apply Subtype.ext
      apply Units.ext
      ext i j
      exact lowerBlockPair_22 b.val x h i j
  right_inv := by
    intro k
    apply Subtype.ext
    apply Units.ext
    ext i j
    change lowerBlockPair (lowerTriangularFirstBlock k).val (lowerTriangularRectangle k)
      (lowerTriangularLastBlock k) i j = k.val.val i j
    induction i using Fin.addCases with
    | left i =>
      induction j using Fin.addCases with
      | left j => rw [lowerBlockPair_11]; rfl
      | right j => rw [lowerBlockPair_12, lowerTriangular_apply_castAdd_natAdd]
    | right i =>
      induction j using Fin.addCases with
      | left j => rw [lowerBlockPair_21]; rfl
      | right j => rw [lowerBlockPair_22]; rfl

@[simp] theorem lowerTriangularBlockEquiv_apply (z : lowerTriangularSubgroup a R ×
    Matrix (Fin d) (Fin a) R × lowerTriangularSubgroup d R) :
    lowerTriangularBlockEquiv a d R z = lowerTriangularBlockMap a d R z := rfl

/-- Product of two lower-block displays. -/
theorem lowerBlockPair_mul_lowerBlockPair (g g' : GeneralLinear a R)
    (x x' : Matrix (Fin d) (Fin a) R) (h h' : lowerTriangularSubgroup d R) :
    lowerBlockPair g x h * lowerBlockPair g' x' h' =
      lowerBlockPair (g * g') (x * g'.val + h.val.val * x') (h * h') := by
  apply Units.ext
  change (Matrix.fromBlocks g.val 0 x h.val.val).submatrix finSumFinEquiv.symm
      finSumFinEquiv.symm *
    (Matrix.fromBlocks g'.val 0 x' h'.val.val).submatrix finSumFinEquiv.symm
      finSumFinEquiv.symm =
    (Matrix.fromBlocks (g * g').val 0 (x * g'.val + h.val.val * x') (h * h').val.val).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

/-- The group law in block coordinates. -/
theorem lowerTriangularBlockMap_mul (z w : lowerTriangularSubgroup a R ×
    Matrix (Fin d) (Fin a) R × lowerTriangularSubgroup d R) :
    lowerTriangularBlockMap a d R z * lowerTriangularBlockMap a d R w =
      lowerTriangularBlockMap a d R (z.1 * w.1, z.2.1 * w.1.val.val + z.2.2.val.val * w.2.1,
        z.2.2 * w.2.2) :=
  Subtype.ext (lowerBlockPair_mul_lowerBlockPair _ _ _ _ _ _)

end Algebra

section Topology

variable [TopologicalSpace R] [IsTopologicalRing R]

/-- The block coordinates are continuous. -/
theorem continuous_lowerTriangularBlockMap :
    Continuous (lowerTriangularBlockMap a d R) :=
  (continuous_lowerBlockPair.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).subtype_mk _

/-- The inverse block coordinates are continuous. -/
theorem continuous_lowerTriangularBlockEquiv_symm :
    Continuous (lowerTriangularBlockEquiv a d R).symm := by
  have hval : Continuous fun k : lowerTriangularSubgroup (a + d) R => k.val.val :=
    Units.continuous_val.comp continuous_subtype_val
  have hinv : Continuous fun k : lowerTriangularSubgroup (a + d) R => (k⁻¹).val.val :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv)
  refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
  · refine Continuous.subtype_mk (Units.continuous_iff.mpr ⟨?_, ?_⟩) _
    · exact hval.matrix_submatrix _ _
    · exact hinv.matrix_submatrix _ _
  · exact hval.matrix_submatrix _ _
  · refine Continuous.subtype_mk (Units.continuous_iff.mpr ⟨?_, ?_⟩) _
    · exact hval.matrix_submatrix _ _
    · exact hinv.matrix_submatrix _ _

/-- Block coordinates `B⁻_a × M_{d×a} × B⁻_d ≃ₜ B⁻_{a+d}`. -/
def lowerTriangularBlockHomeomorph (a d : ℕ) (R : Type u) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] :
    (lowerTriangularSubgroup a R × Matrix (Fin d) (Fin a) R × lowerTriangularSubgroup d R) ≃ₜ
      lowerTriangularSubgroup (a + d) R where
  toEquiv := lowerTriangularBlockEquiv a d R
  continuous_toFun := continuous_lowerTriangularBlockMap
  continuous_invFun := continuous_lowerTriangularBlockEquiv_symm

@[simp] theorem lowerTriangularBlockHomeomorph_apply (z : lowerTriangularSubgroup a R ×
    Matrix (Fin d) (Fin a) R × lowerTriangularSubgroup d R) :
    lowerTriangularBlockHomeomorph a d R z = lowerTriangularBlockMap a d R z := rfl

end Topology

end Langlands.GeneralLinear
