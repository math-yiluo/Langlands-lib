/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# A kernel vector with a unit entry from a corank one minor

Let `B : R^n → R^m` be a matrix over a commutative ring with an invertible minor of size
`|n| - 1`. If the kernel of `B` contains a vector `u` whose scalar multiples are faithful
(`c • u = 0 → c = 0`), then the kernel of `B` contains a vector with an entry equal to `1`
(`Matrix.exists_mulVec_eq_zero_and_eq_one_of_isUnit_det_submatrix`).

Over a non-reduced ring the rank of `B` at the points does not determine its kernel; the
faithful vector `u` is what forces the complementary column of the normal form of `B` to vanish.
-/

@[expose] public section

namespace Matrix

variable {R : Type*} [CommRing R] {m n : Type*} [Fintype n]

/-- **A kernel vector with a unit entry.** Let `B : R^n → R^m` have an invertible `a × a` minor,
with `|n| = a + 1`, and let `u` be a vector of the kernel of `B` with `c • u = 0 → c = 0` for
`c : R`. Then the kernel of `B` contains a vector `w` with `w j = 1` for some `j`.

Let `j` be the column outside the minor and `S` the minor. The rows of the minor cut out the free
rank one submodule spanned by the vector `w` with `w j = 1` whose other coordinates are
`-S⁻¹ B_{•j}`, so `u = u j • w`. Then `u j • B w = 0`, hence `(B w)_r • u = 0` for every `r`, and
`B w = 0` by faithfulness. -/
theorem exists_mulVec_eq_zero_and_eq_one_of_isUnit_det_submatrix {a : ℕ} (B : Matrix m n R)
    (e₁ : Fin a → m) (e₀ : Fin a → n) (hB : IsUnit (B.submatrix e₁ e₀).det)
    (hcard : Fintype.card n = a + 1) (u : n → R) (hu : B *ᵥ u = 0)
    (hinj : ∀ c : R, c • u = 0 → c = 0) :
    ∃ (w : n → R) (j : n), B *ᵥ w = 0 ∧ w j = 1 := by
  classical
  have hne : Nonempty n := Fintype.card_pos_iff.1 (by omega)
  by_cases he₀ : Function.Injective e₀
  swap
  · -- two equal columns: the ring is trivial
    obtain ⟨b, b', hbb', hb⟩ : ∃ b b', e₀ b = e₀ b' ∧ b ≠ b' := by
      simp only [Function.Injective, not_forall] at he₀
      obtain ⟨b, b', h, h'⟩ := he₀
      exact ⟨b, b', h, h'⟩
    have h0 : (B.submatrix e₁ e₀).det = 0 :=
      det_zero_of_column_eq hb fun r ↦ by simp [hbb']
    rw [h0, isUnit_zero_iff] at hB
    obtain ⟨j⟩ := hne
    exact ⟨0, j, by simp, by simp [hB]⟩
  -- the column outside the minor
  have himg : (Finset.univ.image e₀).card = a := by
    rw [Finset.card_image_of_injective _ he₀, Finset.card_univ, Fintype.card_fin]
  obtain ⟨j, -, hj⟩ : ∃ j ∈ (Finset.univ : Finset n), j ∉ Finset.univ.image e₀ := by
    by_contra! h
    have := Finset.card_le_card (fun x _ ↦ h x (Finset.mem_univ x) :
      (Finset.univ : Finset n) ⊆ Finset.univ.image e₀)
    rw [himg, Finset.card_univ, hcard] at this
    omega
  have hj' (b : Fin a) : e₀ b ≠ j := fun h ↦ hj (Finset.mem_image.2 ⟨b, Finset.mem_univ _, h⟩)
  have hrange (i : n) (hi : i ≠ j) : ∃ b, e₀ b = i := by
    by_contra! h
    have hi' : i ∉ Finset.univ.image e₀ := by simpa using h
    have := Finset.card_le_univ (insert i (insert j (Finset.univ.image e₀)))
    rw [Finset.card_insert_of_notMem (by simp [hi, hi']), Finset.card_insert_of_notMem hj,
      himg, hcard] at this
    omega
  set S := B.submatrix e₁ e₀ with hS
  set B₁ : Matrix (Fin a) n R := B.submatrix e₁ id with hB₁
  set E : Matrix n (Fin a) R := (1 : Matrix n n R).submatrix id e₀ with hE
  have hBE : B₁ * E = S := by
    ext r b
    simp [hB₁, hE, hS, mul_apply, one_apply]
  -- every vector is determined by its `j`-coordinate and its coordinates along the minor
  have hdecomp (x : n → R) : x = x j • Pi.single j 1 + E *ᵥ (fun b ↦ x (e₀ b)) := by
    funext i
    by_cases hi : i = j
    · subst hi
      simp [hE, mulVec, dotProduct, fun b ↦ (hj' b).symm]
    · obtain ⟨b, rfl⟩ := hrange i hi
      simp [hE, mulVec, dotProduct, one_apply, he₀.eq_iff, hi]
  set c : Fin a → R := S⁻¹ *ᵥ (B₁ *ᵥ Pi.single j 1) with hc
  set w : n → R := Pi.single j 1 - E *ᵥ c with hw
  have hwj : w j = 1 := by
    simp [hw, hE, mulVec, dotProduct, fun b ↦ (hj' b).symm]
  have hB₁w : B₁ *ᵥ w = 0 := by
    rw [hw, mulVec_sub, mulVec_mulVec, hBE, hc, mulVec_mulVec, mul_nonsing_inv _ hB, one_mulVec,
      sub_self]
  -- `u = u j • w`
  have hB₁u : B₁ *ᵥ u = 0 := by
    funext r
    have := congrFun hu (e₁ r)
    simpa [hB₁, mulVec, dotProduct] using this
  have huw : u = u j • w := by
    have h := hdecomp u
    have h' : B₁ *ᵥ u = u j • (B₁ *ᵥ Pi.single j 1) + S *ᵥ (fun b ↦ u (e₀ b)) := by
      conv_lhs => rw [h]
      rw [mulVec_add, mulVec_smul, mulVec_mulVec, hBE]
    rw [hB₁u] at h'
    have hcoord : (fun b ↦ u (e₀ b)) = -(u j • c) := by
      have h'' : S *ᵥ (fun b ↦ u (e₀ b)) = -(u j • (B₁ *ᵥ Pi.single j 1)) :=
        (neg_eq_of_add_eq_zero_right h'.symm).symm
      rw [hc, ← mulVec_smul, ← mulVec_neg, ← h'', mulVec_mulVec, nonsing_inv_mul _ hB,
        one_mulVec]
    calc u = u j • Pi.single j 1 + E *ᵥ (fun b ↦ u (e₀ b)) := h
      _ = u j • w := by rw [hcoord, hw, mulVec_neg, mulVec_smul, smul_sub, sub_eq_add_neg]
  refine ⟨w, j, ?_, hwj⟩
  -- the remaining coordinates of `B w` vanish by faithfulness
  have hBu : u j • (B *ᵥ w) = 0 := by
    rw [← mulVec_smul, ← huw, hu]
  funext r
  refine hinj _ ?_
  rw [huw, smul_smul, mul_comm, ← smul_eq_mul, ← Pi.smul_apply (u j) (B *ᵥ w) r, hBu]
  simp

end Matrix
