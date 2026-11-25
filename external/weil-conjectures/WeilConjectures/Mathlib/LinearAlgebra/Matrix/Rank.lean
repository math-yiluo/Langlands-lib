/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import WeilConjectures.Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The rank of a matrix through its minors

Over a field, a matrix has rank at least `r` if and only if one of its `r × r` minors does not
vanish. Applied to the images of a matrix over a ring `R` in residue fields, this is what makes
the rank of a matrix of functions lower semicontinuous.

## Main statements

- `Matrix.exists_submatrix_det_ne_zero_of_le_rank` and `Matrix.le_rank_of_submatrix_det_ne_zero`:
  the two directions over a field.
- `Matrix.le_rank_map_iff`: `r ≤ rank (A.map ψ)` for a ring homomorphism `ψ` to a field if and only
  if `ψ` does not kill some `r × r` minor of `A`.
- `Matrix.bddAbove_range_rank_submatrix_iff`: the ranks of the finite square submatrices of a
  matrix with arbitrary row and column index types are bounded if and only if its rows span a
  finite-dimensional space.
- `Matrix.rank_add_rank_eq_card_of_exact`: over a field, the ranks of the two maps of an exact
  sequence add up to the dimension of the middle term.
-/

@[expose] public section

open Module

namespace Matrix

variable {K : Type*} [Field K] {m n : Type*} [Fintype n]

/-- A matrix of rank at least `r` over a field has `r` linearly independent columns. -/
theorem exists_linearIndependent_col_of_le_rank (A : Matrix m n K) {r : ℕ} (h : r ≤ A.rank) :
    ∃ e : Fin r → n, LinearIndependent K fun i ↦ A.col (e i) := by
  classical
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent K (Set.range A.col)
  have : Fintype b := ((Set.finite_range _).subset hb).fintype
  have hcard : Fintype.card b = A.rank := by
    rw [rank_eq_finrank_span_cols, ← hspan, finrank_span_set_eq_card hli, Set.toFinset_card]
  let φ : Fin r → b := fun i ↦ (Fintype.equivFin b).symm (Fin.castLE (hcard ▸ h) i)
  have hφ : Function.Injective φ :=
    (Fintype.equivFin b).symm.injective.comp (Fin.castLE_injective _)
  choose e he using fun i ↦ hb (φ i).2
  refine ⟨e, ?_⟩
  simp_rw [he]
  exact hli.comp φ hφ

/-- A matrix of rank at least `r` over a field has a nonvanishing `r × r` minor. -/
theorem exists_submatrix_det_ne_zero_of_le_rank [Finite m] (A : Matrix m n K) {r : ℕ}
    (h : r ≤ A.rank) : ∃ (e₁ : Fin r → m) (e₂ : Fin r → n), (A.submatrix e₁ e₂).det ≠ 0 := by
  have := Fintype.ofFinite m
  obtain ⟨e₂, h₂⟩ := A.exists_linearIndependent_col_of_le_rank h
  have hB : r ≤ (A.submatrix id e₂)ᵀ.rank := by
    have hc : (A.submatrix id e₂).col = fun i ↦ A.col (e₂ i) := rfl
    rw [rank_transpose, rank_eq_finrank_span_cols, hc, finrank_span_eq_card h₂, Fintype.card_fin]
  obtain ⟨e₁, h₁⟩ := (A.submatrix id e₂)ᵀ.exists_linearIndependent_col_of_le_rank hB
  exact ⟨e₁, e₂, ((isUnit_iff_isUnit_det _).1 (linearIndependent_row_iff_isUnit.1 h₁)).ne_zero⟩

/-- A matrix over a field with a nonvanishing `r × r` minor has rank at least `r`. -/
theorem le_rank_of_submatrix_det_ne_zero (A : Matrix m n K) {r : ℕ} (e₁ : Fin r → m)
    (e₂ : Fin r → n) (h : (A.submatrix e₁ e₂).det ≠ 0) : r ≤ A.rank := by
  have := rank_of_det_ne_zero h
  rw [Fintype.card_fin] at this
  exact this ▸ rank_submatrix_le A e₁ e₂

/-- The image of a matrix `A` over a ring in a field `K` has rank at least `r` if and only if some
`r × r` minor of `A` is not killed by the ring homomorphism `ψ` to `K`. -/
theorem le_rank_map_iff [Finite m] {R : Type*} [CommRing R] (A : Matrix m n R) (ψ : R →+* K)
    (r : ℕ) :
    r ≤ (A.map ψ).rank ↔ ∃ (e₁ : Fin r → m) (e₂ : Fin r → n), ψ (A.submatrix e₁ e₂).det ≠ 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨e₁, e₂, h⟩ ↦ le_rank_of_submatrix_det_ne_zero _ e₁ e₂ ?_⟩
  · obtain ⟨e₁, e₂, h⟩ := exists_submatrix_det_ne_zero_of_le_rank _ h
    exact ⟨e₁, e₂, by rwa [RingHom.map_det]⟩
  · rwa [RingHom.map_det] at h

/-- The ranks of the finite square submatrices of a matrix `A` over a field, with arbitrary
(possibly infinite) row and column index types, are bounded if and only if the rows of `A` span a
finite-dimensional space. This identifies the rank of an infinite matrix, as the supremum of the
ranks of its finite square submatrices, with the dimension of its row space (blueprint
`lemma-hankel-rank-rationality--1`, first step of the proof). -/
theorem bddAbove_range_rank_submatrix_iff {m n : Type*} (A : Matrix m n K) :
    BddAbove (Set.range fun x : Σ r : ℕ, (Fin r → m) × (Fin r → n) ↦
      (A.submatrix x.2.1 x.2.2).rank) ↔
      FiniteDimensional K (Submodule.span K (Set.range A.row)) := by
  classical
  refine ⟨fun ⟨B, hB⟩ ↦ ?_, fun _ ↦ ⟨finrank K (Submodule.span K (Set.range A.row)), ?_⟩⟩
  · by_contra hfd
    obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent K (Set.range A.row)
    have hinf : b.Infinite := fun hfin ↦ hfd (hspan ▸ FiniteDimensional.span_of_finite K hfin)
    let φ : Fin (B + 1) → b := fun i ↦ hinf.natEmbedding _ i
    have hφ : Function.Injective φ :=
      (hinf.natEmbedding _).injective.comp Fin.val_injective
    choose e₁ he₁ using fun i ↦ hb (φ i).2
    have hli' : LinearIndependent K fun i ↦ A.row (e₁ i) := by
      simp_rw [he₁]
      exact hli.comp φ hφ
    have := FiniteDimensional.span_of_finite K (Set.finite_range fun i ↦ A.row (e₁ i))
    obtain ⟨s, hs⟩ := (Submodule.span K (Set.range fun i ↦ A.row (e₁ i)))
      |>.exists_finset_injective_funLeft_domRestrict
    have hA' : LinearIndependent K (A.submatrix e₁ ((↑) : s → n)).row :=
      hli'.map (f := LinearMap.funLeft K K ((↑) : s → n)) (LinearMap.injective_domRestrict_iff.1 hs)
    obtain ⟨e₁', e₂', hdet⟩ :=
      (A.submatrix e₁ ((↑) : s → n)).exists_submatrix_det_ne_zero_of_le_rank (r := B + 1)
        (by simp [hA'.rank_matrix])
    have hle := hB ⟨⟨B + 1, e₁ ∘ e₁', (↑) ∘ e₂'⟩, rfl⟩
    dsimp only at hle
    rw [← submatrix_submatrix] at hle
    rw [rank_of_det_ne_zero hdet, Fintype.card_fin] at hle
    omega
  · rintro _ ⟨⟨r, e₁, e₂⟩, rfl⟩
    have := FiniteDimensional.span_of_finite K (Set.finite_range fun i ↦ A.row (e₁ i))
    dsimp only
    rw [rank_eq_finrank_span_row]
    calc finrank K (Submodule.span K (Set.range (A.submatrix e₁ e₂).row))
        = finrank K ((Submodule.span K (Set.range fun i ↦ A.row (e₁ i))).map
            (LinearMap.funLeft K K e₂)) := by
          rw [Submodule.map_span, ← Set.range_comp]
          rfl
      _ ≤ finrank K (Submodule.span K (Set.range fun i ↦ A.row (e₁ i))) :=
          Submodule.finrank_map_le _ _
      _ ≤ finrank K (Submodule.span K (Set.range A.row)) :=
          Submodule.finrank_mono (Submodule.span_mono (Set.range_comp_subset_range _ _))

section Exact

variable {ι₀ ι₁ ι₂ : Type*} [Fintype ι₀] [Fintype ι₁]

/-- **Ranks in an exact sequence over a field.** If `B * A = 0` and every vector killed by `B` is
in the image of `A`, then `rank A + rank B` is the size of the middle term. -/
theorem rank_add_rank_eq_card_of_exact (A : Matrix ι₁ ι₀ K) (B : Matrix ι₂ ι₁ K)
    (hBA : B * A = 0) (h : ∀ v : ι₁ → K, B *ᵥ v = 0 → ∃ w, A *ᵥ w = v) :
    A.rank + B.rank = Fintype.card ι₁ := by
  have hker : LinearMap.ker B.mulVecLin = LinearMap.range A.mulVecLin := by
    refine le_antisymm (fun v hv ↦ ?_) ?_
    · obtain ⟨w, hw⟩ := h v hv
      exact ⟨w, hw⟩
    · rintro _ ⟨w, rfl⟩
      change B *ᵥ (A *ᵥ w) = 0
      rw [Matrix.mulVec_mulVec, hBA, Matrix.zero_mulVec]
  have := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  rw [hker, Module.finrank_fintype_fun_eq_card] at this
  rw [Matrix.rank, Matrix.rank]
  omega

end Exact

end Matrix
