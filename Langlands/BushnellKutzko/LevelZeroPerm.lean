import Langlands.BushnellKutzko.LevelZeroTheta

/-! # Block permutation matrices -/

open Matrix

noncomputable section

namespace Langlands.BushnellKutzko.LevelZero

universe uF

variable {F : Type uF} [Field F] {e f : ℕ}

/-- The relabelling of indices by a permutation of the blocks. -/
def blockPerm (w : Equiv.Perm (Fin e)) : Equiv.Perm (Fin f × Fin e) :=
  Equiv.prodCongr (Equiv.refl (Fin f)) w

@[simp] theorem blockPerm_apply (w : Equiv.Perm (Fin e)) (p : Fin f × Fin e) :
    blockPerm (f := f) w p = (p.1, w p.2) := rfl

@[simp] theorem blockPerm_symm_apply (w : Equiv.Perm (Fin e)) (p : Fin f × Fin e) :
    (blockPerm (f := f) w).symm p = (p.1, w.symm p.2) := rfl

variable (F) in
/-- The block permutation matrix sending the block `i` to the block `w i`. -/
def permGL (w : Equiv.Perm (Fin e)) : GL (Fin f × Fin e) F :=
  ⟨(blockPerm (f := f) w).symm.toPEquiv.toMatrix, (blockPerm (f := f) w).toPEquiv.toMatrix,
    by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp,
    by rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]; simp⟩

theorem coe_permGL (w : Equiv.Perm (Fin e)) :
    ((permGL F (f := f) w : GL (Fin f × Fin e) F) : Matrix (Fin f × Fin e) (Fin f × Fin e) F) =
      (blockPerm (f := f) w).symm.toPEquiv.toMatrix := rfl

theorem coe_permGL_inv (w : Equiv.Perm (Fin e)) :
    (((permGL F (f := f) w)⁻¹ : GL (Fin f × Fin e) F) :
      Matrix (Fin f × Fin e) (Fin f × Fin e) F) = (blockPerm (f := f) w).toPEquiv.toMatrix := rfl

theorem permGL_one : permGL F (f := f) (1 : Equiv.Perm (Fin e)) = 1 := by
  ext1
  rw [coe_permGL]
  have : (blockPerm (f := f) (1 : Equiv.Perm (Fin e))).symm = Equiv.refl _ := by
    ext p <;> simp [Equiv.Perm.one_def]
  rw [this]
  simp

theorem permGL_mul (w₁ w₂ : Equiv.Perm (Fin e)) :
    permGL F (f := f) (w₁ * w₂) = permGL F w₁ * permGL F w₂ := by
  ext1
  rw [Units.val_mul, coe_permGL, coe_permGL, coe_permGL, ← PEquiv.toMatrix_trans,
    ← Equiv.toPEquiv_trans]
  congr 2

/-- Conjugation by a block permutation matrix relabels the blocks. -/
theorem permGL_conj (w : Equiv.Perm (Fin e)) (x : Matrix (Fin f × Fin e) (Fin f × Fin e) F) :
    ((permGL F w : GL (Fin f × Fin e) F) : Matrix (Fin f × Fin e) (Fin f × Fin e) F) * x *
        (((permGL F w)⁻¹ : GL (Fin f × Fin e) F) : Matrix (Fin f × Fin e) (Fin f × Fin e) F) =
      x.submatrix (blockPerm w).symm (blockPerm w).symm := by
  rw [coe_permGL, coe_permGL_inv, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rfl

theorem permGL_swap {i j : Fin e} (hij : i ≠ j) :
    permGL F (f := f) (Equiv.swap i j) = pairGL hij swapU := by
  ext1
  rw [coe_permGL, coe_pairGL, coe_swapU, pairEmb_swap_eq]
  congr 2

theorem pairGL_eq_of_eq {i j i' j' : Fin e} (hij : i ≠ j) (hij' : i' ≠ j') (hi : i = i')
    (hj : j = j') (u : GL (Fin f ⊕ Fin f) F) : pairGL hij u = pairGL hij' u := by
  subst hi hj; rfl

/-- Conjugating a two-block element by a block permutation moves it to the image blocks. -/
theorem permGL_conj_pairGL (w : Equiv.Perm (Fin e)) {i j : Fin e} (hij : i ≠ j)
    (u : GL (Fin f ⊕ Fin f) F) :
    permGL F w * pairGL hij u * (permGL F w)⁻¹ = pairGL (w.injective.ne hij) u := by
  ext1
  rw [Units.val_mul, Units.val_mul, permGL_conj, coe_pairGL, coe_pairGL]
  ext p q
  rw [Matrix.submatrix_apply]
  refine pairEmb_forall (w.injective.ne hij) _
    (fun p q x => pairEmb F hij (u : Matrix (Fin f ⊕ Fin f) (Fin f ⊕ Fin f) F)
      ((blockPerm w).symm p) ((blockPerm w).symm q) = x) ?_ ?_ ?_ ?_ ?_ p q
  · intro a b; simp
  · intro a b; simp
  · intro a b; simp
  · intro a b; simp
  · rintro ⟨a, k⟩ ⟨b, l⟩ h
    simp only [blockPerm_symm_apply]
    rcases h with ⟨hki, hkj⟩ | ⟨hli, hlj⟩
    · have h1 : w.symm k ≠ i := fun h => hki (by rw [← h]; simp)
      have h2 : w.symm k ≠ j := fun h => hkj (by rw [← h]; simp)
      rw [pairEmb_rest_left hij _ _ _ h1 h2]
      by_cases hpq : (a, k) = (b, l)
      · simp only [Prod.mk.injEq] at hpq
        obtain ⟨rfl, rfl⟩ := hpq
        simp
      · rw [Matrix.one_apply_ne hpq, Matrix.one_apply_ne]
        intro h
        simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
        exact hpq (by rw [h.1, h.2])
    · have h1 : w.symm l ≠ i := fun h => hli (by rw [← h]; simp)
      have h2 : w.symm l ≠ j := fun h => hlj (by rw [← h]; simp)
      rw [pairEmb_rest_right hij _ _ _ h1 h2]
      by_cases hpq : (a, k) = (b, l)
      · simp only [Prod.mk.injEq] at hpq
        obtain ⟨rfl, rfl⟩ := hpq
        simp
      · rw [Matrix.one_apply_ne hpq, Matrix.one_apply_ne]
        intro h
        simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
        exact hpq (by rw [h.1, h.2])

end Langlands.BushnellKutzko.LevelZero
