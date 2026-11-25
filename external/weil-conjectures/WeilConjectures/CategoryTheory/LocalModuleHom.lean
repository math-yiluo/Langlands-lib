/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.SheafHom

/-! # Local morphisms of module sheaves

Source: Stacks Project, Modules on Sites, Tag 093T, proof of (1).
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Opposite

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} (M N : SheafOfModules.{u} R)

set_option backward.isDefEq.respectTransparency false in
/-- The linear local morphisms inside the presheaf of additive local morphisms. -/
def localHomSubfunctor : Subfunctor (presheafHom M.val.presheaf N.val.presheaf) where
  obj U := {a | ∀ (V : Over U.unop) (r : R.obj.obj (op V.left))
    (x : M.val.obj (op V.left)), a.app (op V) (r • x) =
      r • (show N.val.obj (op V.left) from a.app (op V) x)}
  map f _a ha V r x := ha ((Over.map f.unop).obj V) r x

/-- Local module morphisms, with restriction by precomposition on slices. -/
abbrev localHom : Cᵒᵖ ⥤ Type u := (localHomSubfunctor M N).toFunctor

/-- The concrete local morphisms are exactly morphisms on the ringed slice. -/
def localHomEquiv (U : Cᵒᵖ) :
    (localHom M N).obj U ≃ (M.over U.unop ⟶ N.over U.unop) where
  toFun a := ⟨PresheafOfModules.homMk a.1 (fun V r x ↦ a.2 V.unop r x)⟩
  invFun a := ⟨(PresheafOfModules.toPresheaf _).map a.val,
    fun V r x ↦ (a.val.app (op V)).hom.map_smul r x⟩
  left_inv a := by apply Subtype.ext; apply NatTrans.ext; funext V; ext x; rfl
  right_inv a := by ext V x; rfl

lemma localHomEquiv_map_app {U V : C} (f : V ⟶ U)
    (a : (localHom M N).obj (op U)) (x : M.val.obj (op V)) :
    (localHomEquiv M N (op V) ((localHom M N).map f.op a)).val.app
        (op (Over.mk (𝟙 V))) x =
      (localHomEquiv M N (op U) a).val.app (op (Over.mk f)) x :=
  ConcreteCategory.congr_hom (presheafHom_map_app (𝟙 V) f f (Category.id_comp f) a.val) x

end SheafOfModules
