/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

@[expose] public section

/-!
# Minors detect linear independence of a finite family of functions

A finite family of functions `v : κ → ι → K` with values in a field is linearly independent if
and only if some square minor `(v i (n j))` of the matrix of the family has nonzero
determinant: finitely many coordinates already witness the independence. Dually, a
finite-dimensional space of functions is separated by finitely many coordinates.

## Main statements

- `linearIndependent_iff_exists_det_ne_zero`: a finite family of functions `ι → K` is linearly
  independent if and only if it has a nonvanishing square minor;
  `LinearIndependent.exists_det_ne_zero` is the forward direction.
- `Submodule.exists_finset_eval_injective`: on a finite-dimensional subspace of `ι → K`,
  evaluation at the coordinates in a suitable finite set is injective.
-/

variable {K : Type*} [Field K] {ι : Type*}

/-- Auxiliary version of `LinearIndependent.exists_det_ne_zero` for a family indexed by
`Fin r`, with the family as the *column* index, which is the shape the induction produces. -/
private theorem exists_det_ne_zero_fin {r : ℕ} {v : Fin r → ι → K} (hv : LinearIndependent K v) :
    ∃ n : Fin r → ι, (Matrix.of fun i j ↦ v j (n i)).det ≠ 0 := by
  induction r with
  | zero => exact ⟨Fin.elim0, by simp⟩
  | succ r ih =>
    obtain ⟨n₀, hn₀⟩ := ih (hv.comp Fin.castSucc (Fin.castSucc_injective r))
    by_contra! hcon
    -- the cofactors of the last row do not depend on the last index
    let c : Fin (r + 1) → K := fun j ↦ (-1) ^ ((Fin.last r : ℕ) + (j : ℕ)) *
      (Matrix.of fun i j' : Fin r ↦ v (j.succAbove j') (n₀ i)).det
    have key : ∀ m : ι, ∑ j, c j * v j m = 0 := by
      intro m
      have h := hcon (Fin.snoc n₀ m : Fin (r + 1) → ι)
      rw [Matrix.det_succ_row _ (Fin.last r)] at h
      rw [← h]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      have hsub : (Matrix.of fun i j ↦ v j ((Fin.snoc n₀ m : Fin (r + 1) → ι) i)).submatrix
            (Fin.last r).succAbove j.succAbove
          = Matrix.of fun i j' : Fin r ↦ v (j.succAbove j') (n₀ i) := by
        ext i j'
        simp
      rw [hsub]
      simp only [c, Matrix.of_apply, Fin.snoc_last]
      ring
    have hc0 : ∀ j, c j = 0 := by
      refine Fintype.linearIndependent_iff.mp hv c (funext fun m ↦ ?_)
      simpa [Finset.sum_apply] using key m
    have hlast := hc0 (Fin.last r)
    simp only [c, Fin.succAbove_last] at hlast
    rcases mul_eq_zero.mp hlast with h1 | h2
    · exact pow_ne_zero _ (by simp) h1
    · exact hn₀ h2

/-- Finitely many coordinates detect linear independence of a finite family of functions:
a family `v : κ → ι → K` is linearly independent if and only if there are coordinates
`n : κ → ι` such that the square matrix `(v i (n j))` has nonzero determinant. -/
theorem linearIndependent_iff_exists_det_ne_zero {κ : Type*} [Fintype κ] [DecidableEq κ]
    {v : κ → ι → K} :
    LinearIndependent K v ↔ ∃ n : κ → ι, (Matrix.of fun i j ↦ v i (n j)).det ≠ 0 := by
  constructor
  · intro hv
    let e := Fintype.equivFin κ
    obtain ⟨n, hn⟩ := exists_det_ne_zero_fin (hv.comp e.symm e.symm.injective)
    refine ⟨n ∘ e, ?_⟩
    have hB : (Matrix.of fun i j ↦ v i ((n ∘ e) j))
        = ((Matrix.of fun i j ↦ (v ∘ e.symm) j (n i)).submatrix e e).transpose := by
      ext i j
      simp
    rw [hB, Matrix.det_transpose, Matrix.det_submatrix_equiv_self]
    exact hn
  · rintro ⟨n, hn⟩
    exact LinearIndependent.of_comp (v := v) (LinearMap.funLeft K K n)
      (Matrix.linearIndependent_rows_of_det_ne_zero hn)

/-- Finitely many coordinates detect linear independence of a finite family of functions:
if `v : κ → ι → K` is linearly independent, then there are coordinates `n : κ → ι` such that
the square matrix `(v i (n j))` has nonzero determinant. -/
theorem LinearIndependent.exists_det_ne_zero {κ : Type*} [Fintype κ] [DecidableEq κ]
    {v : κ → ι → K} (hv : LinearIndependent K v) :
    ∃ n : κ → ι, (Matrix.of fun i j ↦ v i (n j)).det ≠ 0 :=
  linearIndependent_iff_exists_det_ne_zero.mp hv

/-- A finite-dimensional space of functions is separated by finitely many coordinates:
evaluation at the coordinates in a suitable finite set `s` is injective. -/
theorem Submodule.exists_finset_eval_injective (V : Submodule K (ι → K))
    [FiniteDimensional K V] :
    ∃ s : Finset ι, Function.Injective fun (x : V) (j : s) ↦ (x : ι → K) (j : ι) := by
  classical
  have hb : LinearIndependent K fun i ↦ ((Module.finBasis K V i : V) : ι → K) :=
    (Module.finBasis K V).linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  obtain ⟨n, hn⟩ := hb.exists_det_ne_zero
  have hinj : Function.Injective ((LinearMap.funLeft K K n).comp V.subtype) :=
    LinearMap.injective_of_linearIndependent (Module.finBasis K V).span_eq
      (Matrix.linearIndependent_rows_of_det_ne_zero hn)
  refine ⟨Finset.image n Finset.univ, fun x y hxy ↦ hinj (funext fun k ↦ ?_)⟩
  exact congrFun hxy ⟨n k, Finset.mem_image_of_mem n (Finset.mem_univ k)⟩

/-- A finite-dimensional space of functions is separated by finitely many coordinates: there
is a finite set `s` of coordinates such that two elements agreeing on `s` are equal. -/
theorem Submodule.exists_finset_eq_of_forall_apply_eq (V : Submodule K (ι → K))
    [FiniteDimensional K V] :
    ∃ s : Finset ι, ∀ x ∈ V, ∀ y ∈ V, (∀ j ∈ s, x j = y j) → x = y := by
  obtain ⟨s, hs⟩ := V.exists_finset_eval_injective
  refine ⟨s, fun x hx y hy hxy ↦ ?_⟩
  exact congrArg Subtype.val (hs (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) (funext fun j ↦ hxy j.1 j.2))
