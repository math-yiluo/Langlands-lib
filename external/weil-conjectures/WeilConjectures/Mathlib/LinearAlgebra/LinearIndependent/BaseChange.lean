/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

/-!
# Base change for linear independence of a finite family of functions

`linearIndependent_algebraMap_comp_iff` says that linear independence of a family of functions
`v : κ → ι → R` is insensitive to base change along `R → S`, provided the type `ι` of
coordinates is finite. This file proves the variant where instead the family is finite and `R`
is a field: finitely many coordinates already witness the independence, by
`linearIndependent_iff_exists_det_ne_zero`, so the finite case applies.

## Main statements

- `linearIndependent_algebraMap_comp_iff'`: linear independence of a finite family of
  functions `ι → K` with values in a field is preserved and reflected by pushing the values
  along an algebra map `K → L` into a domain.
-/

/-- Linear independence of a *finite* family of functions `ι → K` with values in a field is
preserved and reflected by pushing the values along an algebra map into a domain. This is the
counterpart of `linearIndependent_algebraMap_comp_iff`, which assumes instead that the type of
coordinates is finite. -/
theorem linearIndependent_algebraMap_comp_iff' {K L : Type*} [Field K] [CommRing L] [IsDomain L]
    [Algebra K L] {κ ι : Type*} [Finite κ] {v : κ → ι → K} :
    LinearIndependent L (fun i ↦ algebraMap K L ∘ v i) ↔ LinearIndependent K v := by
  classical
  have := Fintype.ofFinite κ
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact LinearIndependent.of_comp (v := v) ((Algebra.linearMap K L).compLeft ι)
      (h.restrict_scalars' K)
  · obtain ⟨n, hn⟩ := h.exists_det_ne_zero
    have h' : LinearIndependent K fun i ↦ v i ∘ n :=
      Matrix.linearIndependent_rows_of_det_ne_zero hn
    exact LinearIndependent.of_comp (v := fun i ↦ algebraMap K L ∘ v i) (LinearMap.funLeft L L n)
      ((linearIndependent_algebraMap_comp_iff (S := L)).2 h')
