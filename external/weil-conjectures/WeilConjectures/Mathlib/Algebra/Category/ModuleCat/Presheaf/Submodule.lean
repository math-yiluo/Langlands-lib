/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule

/-!
# Factoring through a submodule of a presheaf of modules

A morphism of presheaves of modules whose sections all lie in a submodule `N` of the target
factors through the inclusion `N.ι`.
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory

namespace PresheafOfModules.Submodule

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {M L : PresheafOfModules.{v} R} (N : M.Submodule)

/-- A morphism `f : L ⟶ M` whose sections lie in `N` factors through `N.ι`. -/
noncomputable def lift (f : L ⟶ M) (hf : ∀ X x, f.app X x ∈ N.obj X) :
    L ⟶ N.toPresheafOfModules where
  app X := ModuleCat.ofHom ((f.app X).hom.codRestrict (N.obj X) (hf X))
  naturality {X Y} g := by
    ext x
    exact Subtype.ext (PresheafOfModules.naturality_apply f g x)

@[reassoc (attr := simp)]
lemma lift_ι (f : L ⟶ M) (hf : ∀ X x, f.app X x ∈ N.obj X) : N.lift f hf ≫ N.ι = f := rfl

@[simp]
lemma lift_app_apply_val (f : L ⟶ M) (hf : ∀ X x, f.app X x ∈ N.obj X) (X : Cᵒᵖ) (x : L.obj X) :
    ((N.lift f hf).app X x).val = f.app X x := rfl

end PresheafOfModules.Submodule
