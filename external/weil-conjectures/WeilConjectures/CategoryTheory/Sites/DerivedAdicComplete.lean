/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.CategoryTheory.Triangulated.DerivedAdicCompleteCriteria

/-!
# Derived adic completeness of sheaves

A sheaf `F` with values in a preadditive category with countable products is derived
`n`-adically complete as soon as all its sections `F(U)` are
(`CategoryTheory.Sheaf.isDerivedAdicComplete_of_forall`): limits of sheaves are computed
sectionwise, and a morphism of sheaves is an isomorphism if it is so on all sections.
-/

@[expose] public section

namespace CategoryTheory.Sheaf

open Limits

universe v u v' u'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {A : Type u'}
  [Category.{v'} A] [Preadditive A] [HasLimitsOfShape (Discrete ℕ) A]

/-- A sheaf all of whose sections are derived `n`-adically complete is derived `n`-adically
complete. -/
lemma isDerivedAdicComplete_of_forall {n : ℤ} (F : Sheaf J A)
    (h : ∀ U : Cᵒᵖ, IsDerivedAdicComplete n (F.obj.obj U)) : IsDerivedAdicComplete n F :=
  IsDerivedAdicComplete.of_map (fun U : Cᵒᵖ ↦ sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj U)
    (fun f hf ↦ by
      have : IsIso ((sheafToPresheaf J A).map f) := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ hf
      exact isIso_of_reflects_iso f (sheafToPresheaf J A)) h

end CategoryTheory.Sheaf
