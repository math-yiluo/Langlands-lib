import Langlands.Group.GL.MirabolicOppositeProductStatement

/-! # Proof of the opposite-parabolic mirabolic product identity -/

namespace Langlands.GeneralLinear

universe u

namespace MirabolicOppositeProduct

variable {K : Type u} [Field K]

/-- Replacing one identity row by a row with a nonzero pivot, then moving that
row to the prescribed position, gives an invertible matrix. -/
private theorem exists_prescribed_row {n : ℕ} (w : Fin n → K)
    (l p : Fin n) (hp : w p ≠ 0) :
    ∃ q : GeneralLinear n K,
      (∀ j, q l j = w j) ∧
      ∀ i, i ≠ l → i ≠ p → ∀ j, q i j = if i = j then 1 else 0 := by
  classical
  let A : Matrix (Fin n) (Fin n) K := (1 : Matrix (Fin n) (Fin n) K).updateRow p w
  have hsum : (∑ i, w i • (1 : Matrix (Fin n) (Fin n) K) i) = w := by
    ext j
    simp [Matrix.one_apply, eq_comm]
  have hdet : A.det = w p := by
    simpa only [hsum, Matrix.det_one, smul_eq_mul, mul_one] using
      Matrix.det_updateRow_sum (1 : Matrix (Fin n) (Fin n) K) p w
  let Q := A.submatrix (Equiv.swap l p) id
  have hQ : Q.det ≠ 0 := by
    dsimp [Q]
    rw [Matrix.det_permute, hdet]
    by_cases h : l = p
    · subst p
      simpa using hp
    · simpa [Equiv.Perm.sign_swap h] using hp
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero Q hQ, ?_, ?_⟩
  · intro j
    change A (Equiv.swap l p l) j = w j
    simp [A]
  · intro i hil hip j
    change A (Equiv.swap l p i) j = _
    simp [Equiv.swap_apply_of_ne_of_ne hil hip, A, Matrix.one_apply, hip]

/-- Every row of an actual invertible matrix is nonzero. -/
private theorem exists_nonzero_row {n : ℕ} (g : GeneralLinear n K) (i : Fin n) :
    ∃ j, g i j ≠ 0 := by
  by_contra! h
  have hz : (g * g⁻¹) i i = 0 := by
    change (g.val * (g⁻¹).val) i i = 0
    simp [Matrix.mul_apply, h]
  simp at hz

private theorem mem_opposite_iff (a b : ℕ) (ha : 0 < a)
    (q : GeneralLinear (a + b + 1) K) :
    q ∈ (MirabolicOppositeIntersection.shape a b ha).oppositeParabolic K ↔
      ∀ (i : Fin a) (j : Fin (b + 1)),
        q (Fin.castAdd (b + 1) i) (Fin.natAdd a j) = 0 := by
  rw [BlockShape.mem_oppositeParabolic_iff]
  constructor
  · intro h i j
    simpa only [MirabolicOppositeIntersection.shape, BlockShape.binary_index_zero,
      BlockShape.binary_index_one] using
      h (0 : Fin 2) (1 : Fin 2) i j (show (0 : Fin 2) < 1 from by decide)
  · intro h i j x y hij
    fin_cases i <;> fin_cases j
    · exact False.elim (lt_irrefl _ hij)
    · change q ((MirabolicOppositeIntersection.shape a b ha).index (0 : Fin 2) x)
        ((MirabolicOppositeIntersection.shape a b ha).index (1 : Fin 2) y) = 0
      exact (congrArg₂ q
        (BlockShape.binary_index_zero a (b + 1) ha _ x)
        (BlockShape.binary_index_one a (b + 1) ha _ y)).trans (h x y)
    · simp at hij
    · exact False.elim (lt_irrefl _ hij)

private theorem head_ne_tail (a b : ℕ) (i : Fin a) (j : Fin (b + 1)) :
    Fin.castAdd (b + 1) i ≠ Fin.natAdd a j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  have := i.isLt
  omega

/-- Left multiplication by a mirabolic matrix preserves the last row. -/
private theorem mirabolic_mul_last {n : ℕ} (m : mirabolic n K)
    (h : GeneralLinear (n + 1) K) (j : Fin (n + 1)) :
    (m.val * h) (Fin.last n) j = h (Fin.last n) j := by
  change (m.val.val * h.val) (Fin.last n) j = _
  have hm : ∀ k, m.val.val (Fin.last n) k =
      if k = Fin.last n then 1 else 0 := m.property
  simp [Matrix.mul_apply, hm]

end MirabolicOppositeProduct

/-- Actual opposite-parabolic and mirabolic factors are equivalent to the
nonvanishing of the inverse last row on the tail coordinates. -/
theorem mirabolicOppositeProduct : MirabolicOppositeProductStatement.{u} := by
  intro K _ a b ha g
  constructor
  · rintro ⟨r, m, rfl⟩
    let D : GeneralLinear (b + 1) K :=
      (MirabolicOppositeIntersection.shape a b ha).oppositeLeviProjection K
        (r⁻¹) (1 : Fin 2)
    obtain ⟨j, hj⟩ := MirabolicOppositeProduct.exists_nonzero_row D (Fin.last b)
    refine ⟨j, ?_⟩
    rw [mul_inv_rev]
    change ((m⁻¹).val * r.val⁻¹) (Fin.last (a + b)) (Fin.natAdd a j) ≠ 0
    have htail : r.val⁻¹ (Fin.last (a + b)) (Fin.natAdd a j) ≠ 0 := by
      have heval : D (Fin.last b) j =
          r.val⁻¹ (Fin.last (a + b)) (Fin.natAdd a j) := by
        change (r⁻¹).val.val
          ((MirabolicOppositeIntersection.shape a b ha).index (1 : Fin 2) (Fin.last b))
          ((MirabolicOppositeIntersection.shape a b ha).index (1 : Fin 2) j) = _
        exact congrArg₂ (r⁻¹).val.val
          ((BlockShape.binary_index_one a (b + 1) ha _ (Fin.last b)).trans
            (MirabolicOppositeIntersection.tail_last a b))
          (BlockShape.binary_index_one a (b + 1) ha _ j)
      exact fun hz => hj (heval.trans hz)
    have he := MirabolicOppositeProduct.mirabolic_mul_last (m⁻¹) (r.val⁻¹)
      (Fin.natAdd a j)
    exact fun hz => htail (he.symm.trans hz)
  · rintro ⟨k, hk⟩
    obtain ⟨q, hrow, hrest⟩ := MirabolicOppositeProduct.exists_prescribed_row
      (fun j => (g⁻¹) (Fin.last (a + b)) j)
      (Fin.last (a + b)) (Fin.natAdd a k) hk
    have hq : q ∈ (MirabolicOppositeIntersection.shape a b ha).oppositeParabolic K := by
      apply (MirabolicOppositeProduct.mem_opposite_iff a b ha q).mpr
      intro i j
      have hl : Fin.castAdd (b + 1) i ≠ Fin.last (a + b) := by
        rw [← MirabolicOppositeIntersection.tail_last a b]
        exact MirabolicOppositeProduct.head_ne_tail a b i (Fin.last b)
      rw [hrest _ hl (MirabolicOppositeProduct.head_ne_tail a b i k)]
      simp [MirabolicOppositeProduct.head_ne_tail a b i j]
    have hm : q * g ∈ mirabolic (a + b) K := by
      intro j
      have he : (q * g) (Fin.last (a + b)) j =
          (g⁻¹ * g) (Fin.last (a + b)) j := by
        change (q.val * g.val) _ _ = ((g⁻¹).val * g.val) _ _
        simp only [Matrix.mul_apply, hrow]
      rw [he, inv_mul_cancel]
      simp [Matrix.one_apply, eq_comm]
    refine ⟨⟨q⁻¹, Subgroup.inv_mem _ hq⟩, ⟨q * g, hm⟩, ?_⟩
    simp

end Langlands.GeneralLinear
