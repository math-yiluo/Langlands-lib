import Langlands.BushnellKutzko.LevelZeroStandard

/-! # Two-block embeddings and block permutations for the standard principal order -/

open Matrix

noncomputable section

namespace Langlands.BushnellKutzko.LevelZero

universe uF

variable {F : Type uF} [Field F] {e f : ℕ}

/-- Indices outside two given blocks. -/
abbrev PairRest (e f : ℕ) (i j : Fin e) := {p : Fin f × Fin e // p.2 ≠ i ∧ p.2 ≠ j}

/-- The indices of two distinct blocks, followed by the remaining indices. -/
def pairEquiv {i j : Fin e} (hij : i ≠ j) :
    (Fin f ⊕ Fin f) ⊕ PairRest e f i j ≃ Fin f × Fin e where
  toFun
    | .inl (.inl a) => (a, i)
    | .inl (.inr a) => (a, j)
    | .inr p => p.1
  invFun p :=
    if h : p.2 = i then .inl (.inl p.1) else
      if h' : p.2 = j then .inl (.inr p.1) else .inr ⟨p, h, h'⟩
  left_inv := by
    rintro ((a | a) | ⟨p, hp, hp'⟩)
    · simp
    · simp [Ne.symm hij]
    · simp [hp, hp']
  right_inv := by
    rintro ⟨a, k⟩
    by_cases h : k = i
    · subst h; simp
    · by_cases h' : k = j
      · subst h'; simp [h]
      · simp [h, h']

@[simp] theorem pairEquiv_inl_inl {i j : Fin e} (hij : i ≠ j) (a : Fin f) :
    pairEquiv hij (.inl (.inl a)) = (a, i) := rfl

@[simp] theorem pairEquiv_inl_inr {i j : Fin e} (hij : i ≠ j) (a : Fin f) :
    pairEquiv hij (.inl (.inr a)) = (a, j) := rfl

@[simp] theorem pairEquiv_inr {i j : Fin e} (hij : i ≠ j) (p : PairRest e f i j) :
    pairEquiv hij (.inr p) = p.1 := rfl

theorem pairEquiv_symm_left {i j : Fin e} (hij : i ≠ j) (a : Fin f) :
    (pairEquiv hij).symm (a, i) = .inl (.inl a) :=
  (pairEquiv hij).symm_apply_eq.mpr rfl

theorem pairEquiv_symm_right {i j : Fin e} (hij : i ≠ j) (a : Fin f) :
    (pairEquiv hij).symm (a, j) = .inl (.inr a) :=
  (pairEquiv hij).symm_apply_eq.mpr rfl

theorem pairEquiv_symm_rest {i j : Fin e} (hij : i ≠ j) (p : Fin f × Fin e) (hi : p.2 ≠ i)
    (hj : p.2 ≠ j) : (pairEquiv hij).symm p = .inr ⟨p, hi, hj⟩ :=
  (pairEquiv hij).symm_apply_eq.mpr rfl

variable (F) in
/-- The matrix acting by a `2 × 2` block matrix `M` on the blocks `i, j` and as the
identity elsewhere. -/
def pairEmb {i j : Fin e} (hij : i ≠ j) (M : Matrix (Fin f ⊕ Fin f) (Fin f ⊕ Fin f) F) :
    Matrix (Fin f × Fin e) (Fin f × Fin e) F :=
  Matrix.reindex (pairEquiv hij) (pairEquiv hij) (Matrix.fromBlocks M 0 0 1)

theorem pairEmb_one {i j : Fin e} (hij : i ≠ j) :
    pairEmb F (f := f) hij 1 = 1 := by
  simp only [pairEmb, Matrix.fromBlocks_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

theorem pairEmb_mul {i j : Fin e} (hij : i ≠ j) (M N : Matrix (Fin f ⊕ Fin f) (Fin f ⊕ Fin f) F) :
    pairEmb F hij (M * N) = pairEmb F hij M * pairEmb F hij N := by
  simp only [pairEmb, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one]

/-- The two-block embedding as a monoid homomorphism. -/
def pairEmbHom {i j : Fin e} (hij : i ≠ j) :
    Matrix (Fin f ⊕ Fin f) (Fin f ⊕ Fin f) F →* Matrix (Fin f × Fin e) (Fin f × Fin e) F where
  toFun := pairEmb F hij
  map_one' := pairEmb_one hij
  map_mul' := pairEmb_mul hij

/-- The two-block embedding on invertible matrices. -/
def pairGL {i j : Fin e} (hij : i ≠ j) : GL (Fin f ⊕ Fin f) F →* GL (Fin f × Fin e) F :=
  Units.map (pairEmbHom hij)

@[simp] theorem coe_pairGL {i j : Fin e} (hij : i ≠ j) (g : GL (Fin f ⊕ Fin f) F) :
    ((pairGL hij g : GL (Fin f × Fin e) F) : Matrix (Fin f × Fin e) (Fin f × Fin e) F) =
      pairEmb F hij (g : Matrix (Fin f ⊕ Fin f) (Fin f ⊕ Fin f) F) := rfl

theorem pairEmb_apply {i j : Fin e} (hij : i ≠ j) (M : Matrix (Fin f ⊕ Fin f) (Fin f ⊕ Fin f) F)
    (p q : Fin f × Fin e) :
    pairEmb F hij M p q =
      Matrix.fromBlocks M 0 0 1 ((pairEquiv hij).symm p) ((pairEquiv hij).symm q) := rfl

@[simp] theorem pairEmb_ll {i j : Fin e} (hij : i ≠ j) (M : Matrix (Fin f ⊕ Fin f) (Fin f ⊕ Fin f) F)
    (a b : Fin f) : pairEmb F hij M (a, i) (b, i) = M (.inl a) (.inl b) := by
  simp [pairEmb_apply, pairEquiv_symm_left]

@[simp] theorem pairEmb_lr {i j : Fin e} (hij : i ≠ j) (M : Matrix (Fin f ⊕ Fin f) (Fin f ⊕ Fin f) F)
    (a b : Fin f) : pairEmb F hij M (a, i) (b, j) = M (.inl a) (.inr b) := by
  simp [pairEmb_apply, pairEquiv_symm_left, pairEquiv_symm_right]

@[simp] theorem pairEmb_rl {i j : Fin e} (hij : i ≠ j) (M : Matrix (Fin f ⊕ Fin f) (Fin f ⊕ Fin f) F)
    (a b : Fin f) : pairEmb F hij M (a, j) (b, i) = M (.inr a) (.inl b) := by
  simp [pairEmb_apply, pairEquiv_symm_left, pairEquiv_symm_right]

@[simp] theorem pairEmb_rr {i j : Fin e} (hij : i ≠ j) (M : Matrix (Fin f ⊕ Fin f) (Fin f ⊕ Fin f) F)
    (a b : Fin f) : pairEmb F hij M (a, j) (b, j) = M (.inr a) (.inr b) := by
  simp [pairEmb_apply, pairEquiv_symm_right]

theorem pairEmb_rest_left {i j : Fin e} (hij : i ≠ j)
    (M : Matrix (Fin f ⊕ Fin f) (Fin f ⊕ Fin f) F) (p q : Fin f × Fin e)
    (hi : p.2 ≠ i) (hj : p.2 ≠ j) : pairEmb F hij M p q = (1 : Matrix _ _ F) p q := by
  rw [pairEmb_apply, pairEquiv_symm_rest hij p hi hj]
  by_cases hqi : q.2 = i
  · obtain ⟨b, k⟩ := q
    simp only at hqi
    subst hqi
    rw [pairEquiv_symm_left]
    have : p ≠ (b, k) := fun h => hi (by rw [h])
    simp [Matrix.one_apply_ne this]
  · by_cases hqj : q.2 = j
    · obtain ⟨b, k⟩ := q
      simp only at hqj
      subst hqj
      rw [pairEquiv_symm_right]
      have : p ≠ (b, k) := fun h => hj (by rw [h])
      simp [Matrix.one_apply_ne this]
    · rw [pairEquiv_symm_rest hij q hqi hqj]
      simp only [Matrix.fromBlocks_apply₂₂]
      by_cases hpq : p = q
      · subst hpq; simp
      · rw [Matrix.one_apply_ne hpq, Matrix.one_apply_ne]
        intro h
        exact hpq (congrArg Subtype.val h)

theorem pairEmb_rest_right {i j : Fin e} (hij : i ≠ j)
    (M : Matrix (Fin f ⊕ Fin f) (Fin f ⊕ Fin f) F) (p q : Fin f × Fin e)
    (hi : q.2 ≠ i) (hj : q.2 ≠ j) : pairEmb F hij M p q = (1 : Matrix _ _ F) p q := by
  by_cases hpi : p.2 = i
  · rw [pairEmb_apply, pairEquiv_symm_rest hij q hi hj]
    obtain ⟨b, k⟩ := p
    simp only at hpi
    subst hpi
    rw [pairEquiv_symm_left]
    have : (b, k) ≠ q := fun h => hi (by rw [← h])
    simp [Matrix.one_apply_ne this]
  · by_cases hpj : p.2 = j
    · rw [pairEmb_apply, pairEquiv_symm_rest hij q hi hj]
      obtain ⟨b, k⟩ := p
      simp only at hpj
      subst hpj
      rw [pairEquiv_symm_right]
      have : (b, k) ≠ q := fun h => hj (by rw [← h])
      simp [Matrix.one_apply_ne this]
    · exact pairEmb_rest_left hij M p q hpi hpj

end Langlands.BushnellKutzko.LevelZero
