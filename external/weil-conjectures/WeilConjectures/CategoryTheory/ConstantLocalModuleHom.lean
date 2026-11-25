/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.LocalModuleIso

/-! # Constant sections of local module Hom and Isom presheaves

Source: Stacks Project, Modules on Sites, Tag 093T.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

universe u v

open CategoryTheory Opposite

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} {D : Type v} [Category.{u} D]
  (F : D ⥤ SheafOfModules.{u} R) (M N P : D)

/-- The canonical constant-presheaf map into local module morphisms. -/
def constantLocalHom : (Functor.const Cᵒᵖ).obj (M ⟶ N) ⟶ localHom (F.obj M) (F.obj N) where
  app U := ↾fun a ↦ (localHomEquiv _ _ U).symm ((overFunctor R U.unop).map (F.map a))
  naturality {U V} f := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Subtype.ext
    apply NatTrans.ext
    funext W
    ext x
    rfl

lemma constantLocalHom_equiv (U : Cᵒᵖ) (a : M ⟶ N) :
    localHomEquiv _ _ U ((constantLocalHom F M N).app U a) =
      (overFunctor R U.unop).map (F.map a) :=
  (localHomEquiv _ _ U).apply_symm_apply _

end SheafOfModules
