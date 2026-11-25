/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Idempotents.FunctorExtension
public import WeilConjectures.CategoryTheory.StageSystem.Functor

/-! # Karoubi extension of systems, morphisms and compatible transformations

The extension is defined by the supported projector formulas of Mathlib.
Source: sketch32, lines 1208--1228 and 1313--1321.
(blueprint: lem-sbc-stage-system-karoubi-extension)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Idempotents

namespace CategoryTheory.StageSystem
variable {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]

/-- Systems are equal when their transition and associator data agree. -/
theorem system_ext {S T : StageSystem C} (hT : @S.T = @T.T)
    (ha : HEq (@S.assoc) (@T.assoc)) : S = T := by
  cases S
  cases T
  cases hT
  cases ha
  rfl

/-- Extend a scalar system by the supported Karoubi formulas. -/
def karSystem (S : StageSystem C) : StageSystem (fun i ↦ Karoubi (C i)) where
  T h := (functorExtension₂ _ _).obj (S.T h)
  assoc h k := (functorExtension₂ _ _).mapIso (S.assoc h k)
  cocycle {i j k m} h h' h'' P := by
    have he :
        Functor.whiskerRight ((functorExtension₂ _ _).map (S.assoc h h').hom)
            ((functorExtension₂ _ _).obj (S.T h'')) ≫
          (functorExtension₂ _ _).map (S.assoc (h.trans h') h'').hom =
        Functor.whiskerLeft ((functorExtension₂ _ _).obj (S.T h))
            ((functorExtension₂ _ _).map (S.assoc h' h'').hom) ≫
          (functorExtension₂ _ _).map (S.assoc h (h'.trans h'')).hom := by
      apply (whiskeringLeftObjToKaroubiFullyFaithful (C := C i) (D := Karoubi (C m))).map_injective
      ext K
      simp only [Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app,
        NatTrans.comp_app, Functor.whiskerRight_app]
      simpa [Functor.map_comp, functorExtension₂, functorExtension₁,
        FunctorExtension₁.obj, FunctorExtension₁.map] using S.cocycle h h' h'' K
    exact congrArg (fun α ↦ α.app P) he
end CategoryTheory.StageSystem

namespace CategoryTheory.StageSystem
universe u' v'
variable {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
  {D : I → Type u'} [∀ i, Category.{v'} (D i)]
  {S : StageSystem C} {T : StageSystem D}

end CategoryTheory.StageSystem

namespace CategoryTheory.Idempotents
universe a b x y
variable {A : Type a} [Category.{x} A] {B : Type b} [Category.{y} B]

/-- Additivity of the supported extension follows on underlying arrows. -/
instance extension_additive [Preadditive A] [Preadditive B]
    (F : A ⥤ B) [F.Additive] : ((functorExtension₂ _ _).obj F).Additive where
  map_add := by
    intros
    apply Karoubi.hom_ext
    exact F.map_add

end CategoryTheory.Idempotents

namespace CategoryTheory.StageSystem
universe u' v'
variable {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
  {D : I → Type u'} [∀ i, Category.{v'} (D i)]
  {S : StageSystem C} {T : StageSystem D}
  {S' : StageSystem (fun i ↦ Karoubi (C i))}
  {T' : StageSystem (fun i ↦ Karoubi (D i))}
  (hS : karSystem S = S') (hT : karSystem T = T')

end CategoryTheory.StageSystem

namespace CategoryTheory.StageSystem
universe u' v'
variable {I : Type w} [Preorder I] {C : I → Type u} [∀ i, Category.{v} (C i)]
  {D : I → Type u'} [∀ i, Category.{v'} (D i)]
  {S : StageSystem C} {T : StageSystem D}
  {S' : StageSystem (fun i ↦ Karoubi (C i))}
  {T' : StageSystem (fun i ↦ Karoubi (D i))}

end CategoryTheory.StageSystem
