/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Single morphisms as coverings of the fppf and fpqc topologies over a base

A single flat surjective morphism of schemes over `S`, locally of finite presentation
(respectively quasi-compact), generates a covering sieve of the fppf (respectively fpqc)
topology on `Over S`. Consequently fppf sheaves, and the functors of points of schemes over `S`,
satisfy the sheaf condition for such a morphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

/-- The functor of points of a scheme over `S` satisfies the sheaf condition for a single flat
surjective quasi-compact morphism, the fpqc topology being subcanonical. -/
lemma isSheafFor_singleton_yoneda {S : Scheme.{u}} (J : Over S) {T T' : Over S} (c : T' ⟶ T)
    [Flat c.left] [Surjective c.left] [QuasiCompact c.left] :
    Presieve.IsSheafFor (yoneda.obj J) (.singleton c) := by
  rw [Presieve.isSheafFor_iff_generate]
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := fpqcTopology.over S)
    (yoneda.obj J) _ (singleton_mem_over_fpqcTopology c)

/-- An fppf sheaf on `Over S` satisfies the sheaf condition for a single flat surjective
morphism locally of finite presentation. -/
lemma isSheafFor_singleton_of_fppf {S : Scheme.{u}}
    (P : Sheaf (fppfTopology.over S) (Type (u + 1))) {T T' : Over S} (c : T' ⟶ T)
    [Flat c.left] [Surjective c.left] [LocallyOfFinitePresentation c.left] :
    Presieve.IsSheafFor P.obj (.singleton c) := by
  rw [Presieve.isSheafFor_iff_generate]
  exact (isSheaf_iff_isSheaf_of_type _ _).1 P.property _
    (singleton_mem_over_fppfTopology c)


end AlgebraicGeometry
