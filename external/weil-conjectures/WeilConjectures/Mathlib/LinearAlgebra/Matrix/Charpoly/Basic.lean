/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Substituting a polynomial into a characteristic polynomial

`Matrix.charpoly_comp` computes `M.charpoly.comp q` as the determinant of `q - M`, generalizing
`Matrix.eval_charpoly` from scalars to polynomials.

`Matrix.BlockTriangular.charpoly_of_injective` generalizes `Matrix.charpoly_of_isUpperTriangular`
to a matrix that is block triangular for an injective map `b` from its index type to a linear
order, that is upper triangular after reordering the indices along `b`; in that case its
characteristic polynomial is `∏ i, (X - C (M i i))` and its roots are its diagonal entries.
-/

@[expose] public section

open Polynomial

namespace Matrix

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

/-- Substituting a polynomial `q` into the characteristic polynomial of `M` gives the
determinant of `q - M`. -/
theorem charpoly_comp (M : Matrix n n R) (q : R[X]) :
    M.charpoly.comp q = (Matrix.scalar n q - M.map C).det := by
  rw [show M.charpoly.comp q = eval₂RingHom C q M.charpoly from rfl, Matrix.charpoly,
    RingHom.map_det, Matrix.charmatrix]
  congr
  ext i j
  obtain rfl | hij := eq_or_ne i j <;> simp [*]

section BlockTriangular

variable {α : Type*} [LinearOrder α] {M : Matrix n n R} {b : n → α}

/-- A matrix that is block triangular for an injective map `b` into a linear order is upper
triangular after reordering the indices along `b`, so its characteristic polynomial is the
product of the `X - C (M i i)`. -/
theorem BlockTriangular.charpoly_of_injective (h : M.BlockTriangular b)
    (hb : Function.Injective b) : M.charpoly = ∏ i, (X - C (M i i)) := by
  let e := Equiv.ofInjective b hb
  have hM : (reindex e e M).IsUpperTriangular := by
    intro i j hij
    simp only [reindex_apply, submatrix_apply]
    apply h
    have hi := e.apply_symm_apply i
    have hj := e.apply_symm_apply j
    rw [Subtype.ext_iff] at hi hj
    simp only [e, Equiv.ofInjective_apply] at hi hj
    rw [hi, hj]
    exact hij
  rw [← charpoly_reindex e, charpoly_of_isUpperTriangular _ hM]
  exact Fintype.prod_equiv e.symm _ _ fun i ↦ by simp

/-- The roots of the characteristic polynomial of a matrix that is block triangular for an
injective map into a linear order are its diagonal entries, with multiplicity. -/
theorem BlockTriangular.charpoly_roots_of_injective [IsDomain R] (h : M.BlockTriangular b)
    (hb : Function.Injective b) :
    M.charpoly.roots = Finset.univ.val.map fun i ↦ M i i := by
  rw [h.charpoly_of_injective hb, Finset.prod_eq_multiset_prod,
    show (fun i ↦ X - C (M i i)) = (fun a ↦ X - C a) ∘ fun i ↦ M i i from rfl,
    ← Multiset.map_map, roots_multiset_prod_X_sub_C]

end BlockTriangular

end Matrix
