import Langlands.Representation.RankinSelberg.RankOneExtensionAnalyticData

/-!
# Matrix identities for the rank-one extension cells

Block-matrix identities in `GL_(1+(t+1))` between the upper cell
`u(y) = [I, y; 0, 1]` and the lower block `B(m, x, a) = [m, 0; x, a]`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear Matrix

universe uF

variable {K : Type uF} [Field K] (t : ℕ)

/-- The block coordinates `Fin (t + 1) ⊕ Fin 1` of an element of `GL_(1+(t+1))`. -/
def rankOneExtensionCellBlocks (g : Langlands.GeneralLinear (1 + (t + 1)) K) :
    Matrix (Fin (t + 1) ⊕ Fin 1) (Fin (t + 1) ⊕ Fin 1) K :=
  ((reindex (R := K) (rankOneExtensionCellCoordinates t)).symm g).val

variable {t}

/-- Numeric entries of the lower block `[m, 0; x, a]` in `GL(1 + (t + 1))`. -/
theorem rankOneExtensionLowerBlock_entry (t : ℕ) (m : Langlands.GeneralLinear (t + 1) K)
    (x : Fin (t + 1) → K) (a : Kˣ) (i j : Fin (1 + (t + 1))) :
    rankOneExtensionLowerBlock t m x a i j =
      if hi : i.val < t + 1 then
        if hj : j.val < t + 1 then m ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0
      else if hj : j.val < t + 1 then x ⟨j.val, hj⟩ else a.val := by
  obtain ⟨i, rfl⟩ := (rankOneExtensionCellCoordinates t).surjective i
  obtain ⟨j, rfl⟩ := (rankOneExtensionCellCoordinates t).surjective j
  rw [rankOneExtensionLowerBlock_apply]
  rcases i with i | i <;> rcases j with j | j
  · simp [rankOneExtensionCellCoordinates, Fin.is_le]
  · simp [rankOneExtensionCellCoordinates, Fin.val_eq_zero, not_lt.2 (Fin.is_le i)]
  · simp [rankOneExtensionCellCoordinates, Fin.val_eq_zero, not_lt.2 (Fin.is_le j)]
  · simp [rankOneExtensionCellCoordinates, Fin.val_eq_zero]

theorem rankOneExtensionCellBlocks_mul (g h : Langlands.GeneralLinear (1 + (t + 1)) K) :
    rankOneExtensionCellBlocks t (g * h) =
      rankOneExtensionCellBlocks t g * rankOneExtensionCellBlocks t h := by
  simp [rankOneExtensionCellBlocks]

theorem rankOneExtensionCellBlocks_injective :
    Function.Injective (rankOneExtensionCellBlocks (K := K) t) := by
  intro g h hgh
  apply (reindex (R := K) (rankOneExtensionCellCoordinates t)).symm.injective
  exact Units.ext hgh

theorem rankOneExtensionCellBlocks_upperCell (y : Fin (t + 1) → K) :
    rankOneExtensionCellBlocks t (rankOneExtensionUpperCell t y) =
      Matrix.fromBlocks 1 (Matrix.of fun i (_ : Fin 1) => y i) 0 1 := by
  simp [rankOneExtensionCellBlocks, rankOneExtensionUpperCell]

theorem rankOneExtensionCellBlocks_lowerBlock (m : Langlands.GeneralLinear (t + 1) K)
    (x : Fin (t + 1) → K) (a : Kˣ) :
    rankOneExtensionCellBlocks t (rankOneExtensionLowerBlock t m x a) =
      Matrix.fromBlocks m.val 0 (Matrix.of fun (_ : Fin 1) => x)
        (Matrix.of fun (_ _ : Fin 1) => a.val) := by
  simp [rankOneExtensionCellBlocks, rankOneExtensionLowerBlock]

theorem rankOneExtensionUpperCell_mul (y z : Fin (t + 1) → K) :
    rankOneExtensionUpperCell t y * rankOneExtensionUpperCell t z =
      rankOneExtensionUpperCell t (y + z) := by
  apply rankOneExtensionCellBlocks_injective
  rw [rankOneExtensionCellBlocks_mul, rankOneExtensionCellBlocks_upperCell,
    rankOneExtensionCellBlocks_upperCell, rankOneExtensionCellBlocks_upperCell,
    Matrix.fromBlocks_multiply]
  congr 1 <;> ext i j <;> simp [add_comm]

@[simp] theorem rankOneExtensionUpperCell_zero :
    rankOneExtensionUpperCell t (0 : Fin (t + 1) → K) = 1 := by
  apply rankOneExtensionCellBlocks_injective
  rw [rankOneExtensionCellBlocks_upperCell]
  simp only [rankOneExtensionCellBlocks, map_one, Units.val_one]
  rw [← Matrix.fromBlocks_one]
  congr 1

theorem rankOneExtensionLowerBlock_mul (m m' : Langlands.GeneralLinear (t + 1) K)
    (x x' : Fin (t + 1) → K) (a a' : Kˣ) :
    rankOneExtensionLowerBlock t m x a * rankOneExtensionLowerBlock t m' x' a' =
      rankOneExtensionLowerBlock t (m * m') (x ᵥ* m'.val + (a : K) • x') (a * a') := by
  apply rankOneExtensionCellBlocks_injective
  rw [rankOneExtensionCellBlocks_mul, rankOneExtensionCellBlocks_lowerBlock,
    rankOneExtensionCellBlocks_lowerBlock, rankOneExtensionCellBlocks_lowerBlock,
    Matrix.fromBlocks_multiply]
  congr 1
  · simp
  · simp
  · ext i j
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  · ext i j
    simp [Matrix.mul_apply]

theorem rankOneExtensionLowerBlock_upperCell (n : Langlands.GeneralLinear (t + 1) K)
    (z : Fin (t + 1) → K) :
    rankOneExtensionLowerBlock t n 0 1 * rankOneExtensionUpperCell t z =
      rankOneExtensionUpperCell t (n.val *ᵥ z) * rankOneExtensionLowerBlock t n 0 1 := by
  apply rankOneExtensionCellBlocks_injective
  rw [rankOneExtensionCellBlocks_mul, rankOneExtensionCellBlocks_mul,
    rankOneExtensionCellBlocks_lowerBlock, rankOneExtensionCellBlocks_upperCell,
    rankOneExtensionCellBlocks_upperCell, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  congr 1
  · ext i j
    simp [Matrix.mul_apply]
  · ext i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · ext i j
    simp
  · ext i j
    simp [Matrix.mul_apply]

private theorem mul_col {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    M * (Matrix.of fun i (_ : Fin 1) => v i) = Matrix.of fun i (_ : Fin 1) => (M *ᵥ v) i := by
  ext i j
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

private theorem col_mul_scalar {n : ℕ} (v : Fin n → K) (c : K) :
    (Matrix.of fun i (_ : Fin 1) => v i) * (Matrix.of fun (_ _ : Fin 1) => c) =
      Matrix.of fun i (_ : Fin 1) => (c • v) i := by
  ext i j
  simp [Matrix.mul_apply, mul_comm]

private theorem row_mul_col {n : ℕ} (x v : Fin n → K) :
    (Matrix.of fun (_ : Fin 1) => x) * (Matrix.of fun i (_ : Fin 1) => v i) =
      Matrix.of fun (_ _ : Fin 1) => x ⬝ᵥ v := by
  ext i j
  simp [Matrix.mul_apply, dotProduct]

/-- The open-cell exchange `u(m y₁) B(m, x, a) = B(m', x, a') u(a' y₁)` when
`m' = m (I + y₁ x)` and `a' (1 + x · y₁) = a`. -/
theorem rankOneExtensionUpperCell_mulVec_mul_lowerBlock
    (m m' : Langlands.GeneralLinear (t + 1) K) (x y₁ : Fin (t + 1) → K) (a a' : Kˣ)
    (hm : m'.val = m.val * (1 + Matrix.vecMulVec y₁ x))
    (ha : (a' : K) * (1 + x ⬝ᵥ y₁) = a) :
    rankOneExtensionUpperCell t (m.val *ᵥ y₁) * rankOneExtensionLowerBlock t m x a =
      rankOneExtensionLowerBlock t m' x a' *
        rankOneExtensionUpperCell t ((a' : K) • y₁) := by
  apply rankOneExtensionCellBlocks_injective
  rw [rankOneExtensionCellBlocks_mul, rankOneExtensionCellBlocks_mul,
    rankOneExtensionCellBlocks_lowerBlock, rankOneExtensionCellBlocks_upperCell,
    rankOneExtensionCellBlocks_upperCell, rankOneExtensionCellBlocks_lowerBlock,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  congr 1
  · rw [hm]
    ext i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.vecMulVec, mul_add]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  · have h1 : (m.val * (1 + Matrix.vecMulVec y₁ x)) *ᵥ ((a' : K) • y₁) =
        (a : K) • (m.val *ᵥ y₁) := by
      rw [← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
        Matrix.vecMulVec_mulVec, ← ha]
      ext k
      simp [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_smul]
      ring
    rw [hm]
    simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero]
    rw [mul_col, col_mul_scalar, h1]
  · ext i j
    simp
  · simp only [Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, zero_add]
    rw [row_mul_col]
    ext i j
    simp only [Matrix.add_apply, Matrix.of_apply, dotProduct_smul, smul_eq_mul, ← ha]
    ring

/-- An element of `GL_(1+(t+1))` is recovered from its block coordinates. -/
theorem rankOneExtensionCellBlocks_val (g : Langlands.GeneralLinear (1 + (t + 1)) K) :
    g.val = Matrix.reindex (rankOneExtensionCellCoordinates t) (rankOneExtensionCellCoordinates t)
      (rankOneExtensionCellBlocks t g) := by
  conv_lhs => rw [← (reindex (R := K) (rankOneExtensionCellCoordinates t)).apply_symm_apply g]
  rfl

theorem det_eq_det_rankOneExtensionCellBlocks (g : Langlands.GeneralLinear (1 + (t + 1)) K) :
    g.val.det = (rankOneExtensionCellBlocks t g).det := by
  rw [rankOneExtensionCellBlocks_val g, Matrix.det_reindex_self]

theorem det_rankOneExtensionLowerBlock (m : Langlands.GeneralLinear (t + 1) K)
    (x : Fin (t + 1) → K) (a : Kˣ) :
    (rankOneExtensionLowerBlock t m x a).val.det = m.val.det * a := by
  rw [det_eq_det_rankOneExtensionCellBlocks, rankOneExtensionCellBlocks_lowerBlock,
    Matrix.det_fromBlocks_zero₁₂, Matrix.det_fin_one]
  simp

theorem det_rankOneExtensionUpperCell (y : Fin (t + 1) → K) :
    (rankOneExtensionUpperCell t y).val.det = 1 := by
  rw [det_eq_det_rankOneExtensionCellBlocks, rankOneExtensionCellBlocks_upperCell,
    Matrix.det_fromBlocks_zero₂₁]
  simp

theorem rankOneExtensionCellCoordinates_inl_val (i : Fin (t + 1)) :
    (rankOneExtensionCellCoordinates t (Sum.inl i)).val = i.val := by
  simp [rankOneExtensionCellCoordinates]

theorem rankOneExtensionCellCoordinates_inr_val (j : Fin 1) :
    (rankOneExtensionCellCoordinates t (Sum.inr j)).val = t + 1 + j.val := by
  simp [rankOneExtensionCellCoordinates]
  omega

theorem rankOneExtensionCellBlocks_apply (g : Langlands.GeneralLinear (1 + (t + 1)) K)
    (a b : Fin (t + 1) ⊕ Fin 1) :
    rankOneExtensionCellBlocks t g a b =
      g (rankOneExtensionCellCoordinates t a) (rankOneExtensionCellCoordinates t b) := by
  rw [rankOneExtensionCellBlocks_val g]
  simp [rankOneExtensionCellBlocks]

/-- Upper unipotence read in the block coordinates. -/
theorem mem_upperUnipotent_iff_cellBlocks (g : Langlands.GeneralLinear (1 + (t + 1)) K) :
    g ∈ upperUnipotent (1 + (t + 1)) K ↔
      (∀ a b : Fin (t + 1) ⊕ Fin 1,
        rankOneExtensionCellCoordinates t b < rankOneExtensionCellCoordinates t a →
          rankOneExtensionCellBlocks t g a b = 0) ∧
      ∀ a, rankOneExtensionCellBlocks t g a a = 1 := by
  simp only [rankOneExtensionCellBlocks_apply]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun a b hab => h1 hab, fun a => h2 _⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · obtain ⟨a, rfl⟩ := (rankOneExtensionCellCoordinates t).surjective i
      obtain ⟨b, rfl⟩ := (rankOneExtensionCellCoordinates t).surjective j
      exact h1 a b hij
    · obtain ⟨a, rfl⟩ := (rankOneExtensionCellCoordinates t).surjective i
      exact h2 a

theorem rankOneExtensionUpperCell_mem_upperUnipotent (y : Fin (t + 1) → K) :
    rankOneExtensionUpperCell t y ∈ upperUnipotent (1 + (t + 1)) K := by
  rw [mem_upperUnipotent_iff_cellBlocks, rankOneExtensionCellBlocks_upperCell]
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [Fin.lt_def] at hab
    rcases a with i | i <;> rcases b with j | j
    · have hij : i ≠ j := by
        rintro rfl
        exact lt_irrefl _ hab
      simp [Matrix.one_apply_ne hij]
    · rw [rankOneExtensionCellCoordinates_inl_val, rankOneExtensionCellCoordinates_inr_val] at hab
      omega
    · simp
    · rw [rankOneExtensionCellCoordinates_inr_val, rankOneExtensionCellCoordinates_inr_val] at hab
      omega
  · rcases a with i | i
    · simp
    · simp

theorem rankOneExtensionLowerBlock_mem_upperUnipotent (n : Langlands.GeneralLinear (t + 1) K)
    (hn : n ∈ upperUnipotent (t + 1) K) :
    rankOneExtensionLowerBlock t n 0 1 ∈ upperUnipotent (1 + (t + 1)) K := by
  rw [mem_upperUnipotent_iff_cellBlocks, rankOneExtensionCellBlocks_lowerBlock]
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [Fin.lt_def] at hab
    rcases a with i | i <;> rcases b with j | j
    · rw [rankOneExtensionCellCoordinates_inl_val, rankOneExtensionCellCoordinates_inl_val] at hab
      exact hn.1 (show j < i from hab)
    · simp
    · simp
    · rw [rankOneExtensionCellCoordinates_inr_val, rankOneExtensionCellCoordinates_inr_val] at hab
      omega
  · rcases a with i | i
    · exact hn.2 i
    · simp

/-- The top-left block of an upper unipotent element, as an element of `GL_(t+1)`. -/
def rankOneExtensionUnipotentHead (n : upperUnipotent (1 + (t + 1)) K) :
    Langlands.GeneralLinear (t + 1) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    ((rankOneExtensionCellBlocks t n.val).toBlocks₁₁)
    (by
      have hn := (mem_upperUnipotent_iff_cellBlocks n.val).mp n.property
      rw [Matrix.det_of_isUpperTriangular]
      · simp [Matrix.toBlocks₁₁, hn.2]
      · intro i j hij
        exact hn.1 (Sum.inl i) (Sum.inl j) (by
          rw [Fin.lt_def, rankOneExtensionCellCoordinates_inl_val,
            rankOneExtensionCellCoordinates_inl_val]
          exact hij))

/-- The last column of an upper unipotent element, above the diagonal. -/
def rankOneExtensionUnipotentColumn (n : upperUnipotent (1 + (t + 1)) K) : Fin (t + 1) → K :=
  fun i => rankOneExtensionCellBlocks t n.val (Sum.inl i) (Sum.inr 0)

theorem rankOneExtensionUnipotentHead_mem (n : upperUnipotent (1 + (t + 1)) K) :
    rankOneExtensionUnipotentHead n ∈ upperUnipotent (t + 1) K := by
  have hn := (mem_upperUnipotent_iff_cellBlocks n.val).mp n.property
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · exact hn.1 (Sum.inl i) (Sum.inl j) (by
      rw [Fin.lt_def, rankOneExtensionCellCoordinates_inl_val,
        rankOneExtensionCellCoordinates_inl_val]
      exact hij)
  · exact hn.2 (Sum.inl i)

/-- Every upper unipotent element is `u(y₀) B(n'', 0, 1)`. -/
theorem rankOneExtensionUnipotent_decomposition (n : upperUnipotent (1 + (t + 1)) K) :
    n.val = rankOneExtensionUpperCell t (rankOneExtensionUnipotentColumn n) *
      rankOneExtensionLowerBlock t (rankOneExtensionUnipotentHead n) 0 1 := by
  have hn := (mem_upperUnipotent_iff_cellBlocks n.val).mp n.property
  apply rankOneExtensionCellBlocks_injective
  rw [rankOneExtensionCellBlocks_mul, rankOneExtensionCellBlocks_upperCell,
    rankOneExtensionCellBlocks_lowerBlock, Matrix.fromBlocks_multiply]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (rankOneExtensionCellBlocks t n.val)]
  congr 1
  · ext i j
    simp [rankOneExtensionUnipotentHead, Matrix.mul_apply]
  · ext i j
    fin_cases j
    simp [rankOneExtensionUnipotentColumn, Matrix.toBlocks₁₂, Matrix.mul_apply]
  · ext i j
    simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_mul, Matrix.one_mul, zero_add]
    exact hn.1 (Sum.inr i) (Sum.inl j) (by
      rw [Fin.lt_def, rankOneExtensionCellCoordinates_inl_val,
        rankOneExtensionCellCoordinates_inr_val]
      omega)
  · ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.toBlocks₂₂, hn.2]

end Langlands.RankinSelberg
