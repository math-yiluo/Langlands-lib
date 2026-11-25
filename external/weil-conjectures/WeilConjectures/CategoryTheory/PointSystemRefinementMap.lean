/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Canonical maps between colimits of refined diagrams

Source: Stacks Project, Sites, the refinement maps preceding Tag 00YO
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w t r

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Source: Stacks Project, Sites, the refinement maps preceding Tag 00YO
(auxiliary; not a blueprint node).
The canonical map on colimits induced by an inclusion of inverse systems, after applying
any presheaf. The equality `h` identifies the old diagram with the restricted new one.
This is the version for preorder indices; on partial orders it is
`pointSystemRefinementMap`. -/
noncomputable def pointSystemRefinementMapOfPreorder
    {C : Type u} [Category.{v} C]
    {J : Type w} [Preorder J] {I : Type r} [Preorder I]
    (V : J ⥤ Cᵒᵖ) (U : I ⥤ Cᵒᵖ) (e : J ↪o I)
    (h : V = e.monotone.functor ⋙ U) (P : Cᵒᵖ ⥤ Type t)
    [HasColimit (V ⋙ P)] [HasColimit (e.monotone.functor ⋙ (U ⋙ P))]
    [HasColimit (U ⋙ P)] : colimit (V ⋙ P) ⟶ colimit (U ⋙ P) :=
  colimMap (Functor.whiskerRight (eqToHom h) P ≫
    (Functor.associator e.monotone.functor U P).hom) ≫
      colimit.pre (U ⋙ P) e.monotone.functor

/-- Source: Stacks Project, Sites, the refinement maps preceding Tag 00YO
(auxiliary; not a blueprint node).
The canonical map on colimits induced by an inclusion of inverse systems, after applying
any presheaf. The equality `h` identifies the old diagram with the restricted new one. -/
noncomputable def pointSystemRefinementMap
    {C : Type u} [Category.{v} C]
    {J : Type w} [PartialOrder J] {I : Type r} [PartialOrder I]
    (V : J ⥤ Cᵒᵖ) (U : I ⥤ Cᵒᵖ) (e : J ↪o I)
    (h : V = e.monotone.functor ⋙ U) (P : Cᵒᵖ ⥤ Type t)
    [HasColimit (V ⋙ P)] [HasColimit (e.monotone.functor ⋙ (U ⋙ P))]
    [HasColimit (U ⋙ P)] : colimit (V ⋙ P) ⟶ colimit (U ⋙ P) :=
  colimMap (Functor.whiskerRight (eqToHom h) P ≫
    (Functor.associator e.monotone.functor U P).hom) ≫
      colimit.pre (U ⋙ P) e.monotone.functor

/-- On partial orders the two refinement maps agree definitionally. -/
theorem pointSystemRefinementMap_eq_ofPreorder
    {C : Type u} [Category.{v} C]
    {J : Type w} [PartialOrder J] {I : Type r} [PartialOrder I]
    (V : J ⥤ Cᵒᵖ) (U : I ⥤ Cᵒᵖ) (e : J ↪o I)
    (h : V = e.monotone.functor ⋙ U) (P : Cᵒᵖ ⥤ Type t)
    [HasColimit (V ⋙ P)] [HasColimit (e.monotone.functor ⋙ (U ⋙ P))]
    [HasColimit (U ⋙ P)] :
    pointSystemRefinementMap V U e h P = pointSystemRefinementMapOfPreorder V U e h P :=
  rfl

@[simp] theorem pointSystemRefinementMapOfPreorder_ι
    {C : Type u} [Category.{v} C]
    {J : Type w} [Preorder J] {I : Type r} [Preorder I]
    (V : J ⥤ Cᵒᵖ) (U : I ⥤ Cᵒᵖ) (e : J ↪o I)
    (h : V = e.monotone.functor ⋙ U) (P : Cᵒᵖ ⥤ Type t)
    [HasColimit (V ⋙ P)] [HasColimit (e.monotone.functor ⋙ (U ⋙ P))]
    [HasColimit (U ⋙ P)] (j : J) :
    colimit.ι (V ⋙ P) j ≫ pointSystemRefinementMapOfPreorder V U e h P =
      P.map (eqToHom (congrArg (fun T : J ⥤ Cᵒᵖ ↦ T.obj j) h)) ≫
        colimit.ι (U ⋙ P) (e j) := by
  subst V
  simp [pointSystemRefinementMapOfPreorder]

theorem pointSystemRefinementMapOfPreorder_eq
    {C : Type u} [Category.{v} C]
    {J : Type w} [Preorder J] {I : Type r} [Preorder I]
    (V : J ⥤ Cᵒᵖ) (U : I ⥤ Cᵒᵖ) (e : J ↪o I)
    (h : V = e.monotone.functor ⋙ U) (P : Cᵒᵖ ⥤ Type (max w r t))
    :
    pointSystemRefinementMapOfPreorder V U e h P =
      eqToHom (congrArg (fun T : J ⥤ Cᵒᵖ ↦ colimit (T ⋙ P)) h) ≫
        colimit.pre (U ⋙ P) e.monotone.functor := by
  subst V
  apply colimit.hom_ext
  intro j
  calc
    _ = colimit.ι (U ⋙ P) (e j) := by
      simp [pointSystemRefinementMapOfPreorder, ← Category.assoc]
    _ = _ := (colimit.ι_pre (U ⋙ P) e.monotone.functor j).symm

universe z

theorem pointSystemRefinementMapOfPreorder_comp
    {C : Type u} [Category.{v} C]
    {J : Type w} [Preorder J] {I : Type r} [Preorder I]
    {L : Type z} [Preorder L]
    (V : J ⥤ Cᵒᵖ) (U : I ⥤ Cᵒᵖ) (T : L ⥤ Cᵒᵖ)
    (e : J ↪o I) (f : I ↪o L)
    (h : V = e.monotone.functor ⋙ U) (g : U = f.monotone.functor ⋙ T)
    (P : Cᵒᵖ ⥤ Type (max w r z t)) :
    pointSystemRefinementMapOfPreorder V U e h P ≫ pointSystemRefinementMapOfPreorder U T f g P =
      pointSystemRefinementMapOfPreorder V T (e.trans f)
        (h.trans (by rw [g]; rfl)) P := by
  subst V
  subst U
  apply colimit.hom_ext
  intro j
  simp only [← Category.assoc, pointSystemRefinementMapOfPreorder_ι]
  simp
  simpa using pointSystemRefinementMapOfPreorder_ι (f.monotone.functor ⋙ T) T f rfl P (e j)

/-- Refinement maps commute with natural transformations of presheaves. -/
theorem pointSystemRefinementMapOfPreorder_naturality
    {C : Type u} [Category.{v} C]
    {J I : Type w} [Preorder J] [Preorder I]
    (V : J ⥤ Cᵒᵖ) (U : I ⥤ Cᵒᵖ) (e : J ↪o I)
    (h : V = e.monotone.functor ⋙ U)
    {P Q : Cᵒᵖ ⥤ Type (max w t)} (α : P ⟶ Q) :
    colimMap (V.whiskerLeft α) ≫ pointSystemRefinementMapOfPreorder V U e h Q =
      pointSystemRefinementMapOfPreorder V U e h P ≫ colimMap (U.whiskerLeft α) := by
  subst V
  rw [pointSystemRefinementMapOfPreorder_eq _ _ _ rfl Q,
    pointSystemRefinementMapOfPreorder_eq _ _ _ rfl P]
  simp only [eqToHom_refl, Category.id_comp]
  exact (colimit.pre_map (U.whiskerLeft α) e.monotone.functor).symm

end CategoryTheory
