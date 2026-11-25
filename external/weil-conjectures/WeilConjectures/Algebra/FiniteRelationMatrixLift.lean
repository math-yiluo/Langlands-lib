/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- Finite matrix coefficients over a ring colimit can be represented at one stage.

Source: Stacks Project, Algebra, Tag 05N7, proof of (1).
(blueprint: lem-pc-finite-relation-matrix-lift).

Proof: represent each entry q(e_k)_j at some stage using the concrete filtered
colimit representation theorem. Filteredness gives a common receiving stage for
this finite family, including the empty family since the indexing order is
nonempty. Transport each representative along its map to that stage. Naturality
of the coprojections preserves its image. Define qi by multiplication by the
matrix of transported entries; applying qi to e_k retrieves column k. -/
theorem exists_stage_finite_relation_matrix
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat) (n m : ℕ)
    (q : (Fin m → (colimit F : CommRingCat)) →ₗ[(colimit F : CommRingCat)]
      (Fin n → (colimit F : CommRingCat))) :
    ∃ (i : I) (qi : (Fin m → F.obj i) →ₗ[F.obj i] (Fin n → F.obj i)),
      ∀ (j : Fin n) (k : Fin m),
        (colimit.ι F i).hom (qi (Pi.single k 1) j) = q (Pi.single k 1) j := by
  classical
  have reps (p : Fin n × Fin m) :=
    Concrete.colimit_exists_rep F (q (Pi.single p.2 1) p.1)
  choose i a ha using reps
  obtain ⟨j, hj⟩ := IsFiltered.sup_objs_exists (Finset.univ.image i)
  let f (p : Fin n × Fin m) : i p ⟶ j :=
    (hj (Finset.mem_image_of_mem i (Finset.mem_univ p))).some
  let b (p : Fin n × Fin m) : F.obj j := F.map (f p) (a p)
  have hb (p : Fin n × Fin m) :
      (colimit.ι F j).hom (b p) = q (Pi.single p.2 1) p.1 := by
    exact (ConcreteCategory.congr_hom (colimit.w F (f p)) (a p)).trans (ha p)
  refine ⟨j, Matrix.toLin' (fun r c ↦ b (r, c)), ?_⟩
  intro r c
  simpa only [Matrix.toLin'_apply, Matrix.mulVec_single_one, Matrix.col_apply] using
    hb (r, c)

end ModuleCat
