/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.Diagram.DiagramSiteTopology
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! The module part of the product-site realization.

Source: Stacks Project, Modules on Sites, Tags 03CV and 03DA (blueprint:
lem-weil-pbc-diagram-site-module-equivalence).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of a product module to a vertical component. -/
noncomputable def diagramSiteModuleComponent
    (J C : Type u) [SmallCategory J] [SmallCategory C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{u})
    (F : ringedSiteModules.{u} (diagramSiteRing J C K O)) (j : J) :
    ringedSiteModules.{u} O where
  val := PresheafOfModules.pushforward₀Obj (Prod.sectR (op j) C)
    (diagramSiteRing J C K O).obj F.val
  isSheaf := (diagramSite_isSheaf_iff J C K F.val.presheaf).1 F.isSheaf (op j)

set_option backward.isDefEq.respectTransparency false in
set_option linter.unnecessarySimpa false in
/-- Horizontal structure map on the component modules. -/
noncomputable def diagramSiteModuleArrow
    {J C : Type u} [SmallCategory J] [SmallCategory C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{u})
    (F : ringedSiteModules.{u} (diagramSiteRing J C K O))
    {j k : J} (a : j ⟶ k) :
    diagramSiteModuleComponent J C K O F j ⟶ diagramSiteModuleComponent J C K O F k where
  val :=
    { app U := ModuleCat.ofHom
        { toFun := F.val.map (Prod.mkHom a.op (𝟙 U.unop)).op
          map_add' := map_add _
          map_smul' := by
            intro r x
            have H := F.val.map_smul (Prod.mkHom a.op (𝟙 U.unop)).op r x
            simpa [diagramSiteRing, Prod.snd] using H }
      naturality := by
        intro U V f
        ext x
        simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
        change F.val.map (Prod.mkHom a.op (𝟙 V.unop)).op
          (F.val.map ((Prod.sectR (op j) C).op.map f) x) =
          F.val.map ((Prod.sectR (op k) C).op.map f)
            (F.val.map (Prod.mkHom a.op (𝟙 U.unop)).op x)
        have H : ((Prod.sectR (op j) C).op.map f) ≫
            (Prod.mkHom a.op (𝟙 V.unop)).op =
            (Prod.mkHom a.op (𝟙 U.unop)).op ≫ (Prod.sectR (op k) C).op.map f := by
          apply Quiver.Hom.unop_inj
          ext <;> simp
        have HH := F.val.presheaf.congr_map H
        rw [Functor.map_comp, Functor.map_comp] at HH
        exact ConcreteCategory.congr_hom HH x }

set_option backward.isDefEq.respectTransparency false in
/-- The functor restricting module sheaves to component modules. -/
noncomputable def diagramSiteModuleCurry
    (J C : Type u) [SmallCategory J] [SmallCategory C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{u}) :
    ringedSiteModules.{u} (diagramSiteRing J C K O) ⥤ J ⥤ ringedSiteModules.{u} O where
  obj F :=
    { obj j := diagramSiteModuleComponent J C K O F j
      map a := diagramSiteModuleArrow K O F a
      map_id j := by
        ext U x
        change F.val.map (𝟙 (op (op j, U.unop))) x = x
        simp
      map_comp {j k l} a b := by
        ext U x
        change F.val.map (Prod.mkHom (a ≫ b).op (𝟙 U.unop)).op x =
          F.val.map (Prod.mkHom b.op (𝟙 U.unop)).op
            (F.val.map (Prod.mkHom a.op (𝟙 U.unop)).op x)
        rw [← F.val.map_comp_apply]
        apply F.val.congr_map_apply
        apply Quiver.Hom.unop_inj
        ext <;> simp }
  map f :=
    { app j :=
        { val :=
            { app U := f.val.app ((Prod.sectR (op j) C).op.obj U)
              naturality a := f.val.naturality ((Prod.sectR (op j) C).op.map a) } }
      naturality := by
        intro j k a
        ext U x
        exact (PresheafOfModules.naturality_apply f.val (Prod.mkHom a.op (𝟙 U.unop)).op x) }
  map_id F := by ext j U x; rfl
  map_comp f g := by ext j U x; rfl

set_option backward.isDefEq.respectTransparency false in
/-- Assembly of presheaf modules along the two product coordinates. -/
noncomputable def diagramSiteModuleUncurryVal
    {J C : Type u} [SmallCategory J] [SmallCategory C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{u})
    (F : J ⥤ ringedSiteModules.{u} O) :
    PresheafOfModules.{u} (diagramSiteRing J C K O).obj where
  obj X := (F.obj X.unop.1.unop).val.obj (op X.unop.2)
  map {X Y} f := (F.map f.unop.1.unop).val.app (op X.unop.2) ≫
    (F.obj Y.unop.1.unop).val.map f.unop.2.op
  map_id X := by
    ext x
    simp [diagramSiteRing, Prod.snd]
  map_comp {X Y Z} f g := by
    ext x
    change (F.obj Z.unop.1.unop).val.map (f.unop.2.op ≫ g.unop.2.op)
      (((F.map (f.unop.1.unop ≫ g.unop.1.unop)).val.app (op X.unop.2)) x) =
      (F.obj Z.unop.1.unop).val.map g.unop.2.op
        (((F.map g.unop.1.unop).val.app (op Y.unop.2))
          ((F.obj Y.unop.1.unop).val.map f.unop.2.op
            (((F.map f.unop.1.unop).val.app (op X.unop.2)) x)))
    rw [F.map_comp]
    change (F.obj Z.unop.1.unop).val.map (f.unop.2.op ≫ g.unop.2.op)
      (((F.map g.unop.1.unop).val.app (op X.unop.2))
        (((F.map f.unop.1.unop).val.app (op X.unop.2)) x)) = _
    rw [PresheafOfModules.naturality_apply (F.map g.unop.1.unop).val]
    exact (F.obj Z.unop.1.unop).val.map_comp_apply _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Assembly of a diagram of module sheaves to a sheaf on the product site. -/
noncomputable def diagramSiteModuleUncurryObj
    {J C : Type u} [SmallCategory J] [SmallCategory C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{u})
    (F : J ⥤ ringedSiteModules.{u} O) :
    ringedSiteModules.{u} (diagramSiteRing J C K O) where
  val := diagramSiteModuleUncurryVal K O F
  isSheaf := by
    apply (diagramSite_isSheaf_iff J C K _).2
    intro j
    let e : (Prod.sectR j C).op ⋙ (diagramSiteModuleUncurryVal K O F).presheaf ≅
        (F.obj j.unop).val.presheaf :=
      NatIso.ofComponents (fun U ↦ Iso.refl _) (by
        intro U V f
        ext x
        change (F.obj j.unop).val.map f
          (((F.map (𝟙 j.unop)).val.app U) x) = (F.obj j.unop).val.map f x
        simp)
    exact (Presheaf.isSheaf_of_iso_iff e).2 (F.obj j.unop).isSheaf

set_option backward.isDefEq.respectTransparency false in
/-- Assembly is functorial on module morphisms. -/
noncomputable def diagramSiteModuleUncurry
    (J C : Type u) [SmallCategory J] [SmallCategory C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{u}) :
    (J ⥤ ringedSiteModules.{u} O) ⥤ ringedSiteModules.{u} (diagramSiteRing J C K O) where
  obj F := diagramSiteModuleUncurryObj K O F
  map {F G} f :=
    { val :=
        { app X := (f.app X.unop.1.unop).val.app (op X.unop.2)
          naturality := by
            intro X Y a
            ext x
            change ((f.app Y.unop.1.unop).val.app (op Y.unop.2))
              (((F.obj Y.unop.1.unop).val.map a.unop.2.op)
                (((F.map a.unop.1.unop).val.app (op X.unop.2)) x)) =
              ((G.obj Y.unop.1.unop).val.map a.unop.2.op)
                (((G.map a.unop.1.unop).val.app (op X.unop.2))
                  (((f.app X.unop.1.unop).val.app (op X.unop.2)) x))
            rw [PresheafOfModules.naturality_apply (f.app Y.unop.1.unop).val]
            have H := congrArg (fun t ↦ t.val.app (op X.unop.2))
              (f.naturality a.unop.1.unop)
            exact congrArg ((G.obj Y.unop.1.unop).val.map a.unop.2.op)
              (ConcreteCategory.congr_hom H x) } }
  map_id F := by ext X x; rfl
  map_comp f g := by ext X x; rfl

/-- A module-sheaf isomorphism from an isomorphism of its module presheaves. -/
def diagramSiteModuleIso {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
    {O : Sheaf K RingCat.{u}} {F G : ringedSiteModules.{u} O}
    (e : F.val ≅ G.val) : F ≅ G where
  hom := ⟨e.hom⟩
  inv := ⟨e.inv⟩
  hom_inv_id := SheafOfModules.hom_ext e.hom_inv_id
  inv_hom_id := SheafOfModules.hom_ext e.inv_hom_id

set_option backward.isDefEq.respectTransparency false in
/-- The explicit equivalence for modules on the vertical product site. -/
noncomputable def diagramSiteModuleEquivalence
    (J C : Type u) [SmallCategory J] [SmallCategory C]
    (K : GrothendieckTopology C) (O : Sheaf K RingCat.{u}) :
    ringedSiteModules.{u} (diagramSiteRing J C K O) ≌ (J ⥤ ringedSiteModules.{u} O) where
  functor := diagramSiteModuleCurry J C K O
  inverse := diagramSiteModuleUncurry J C K O
  unitIso := NatIso.ofComponents (fun F ↦ diagramSiteModuleIso
    (PresheafOfModules.isoMk (fun X ↦ Iso.refl _) (by
      intro X Y f
      ext x
      change F.val.map f x = F.val.map (Prod.mkHom (𝟙 Y.unop.1) f.unop.2).op
        (F.val.map (Prod.mkHom f.unop.1 (𝟙 X.unop.2)).op x)
      have H : f = (Prod.mkHom f.unop.1 (𝟙 X.unop.2)).op ≫
          (Prod.mkHom (𝟙 Y.unop.1) f.unop.2).op := by
        apply Quiver.Hom.unop_inj
        ext <;> simp
      exact (F.val.congr_map_apply H x).trans (F.val.map_comp_apply _ _ x)))) (by
    intro F G f
    ext X x
    rfl)
  counitIso := NatIso.ofComponents (fun F ↦ NatIso.ofComponents
    (fun j ↦ diagramSiteModuleIso (PresheafOfModules.isoMk (fun U ↦ Iso.refl _) (by
      intro U V f
      ext x
      change (F.obj j).val.map f (((F.map (𝟙 j)).val.app U) x) =
        (F.obj j).val.map f x
      simp))) (by
      intro j k a
      ext U x
      change (F.obj k).val.map (𝟙 U) (((F.map a).val.app U) x) =
        ((F.map a).val.app U) x
      simp)) (by
    intro F G f
    ext j U x
    rfl)
  functor_unitIso_comp F := by
    ext j U x
    rfl

end CategoryTheory
