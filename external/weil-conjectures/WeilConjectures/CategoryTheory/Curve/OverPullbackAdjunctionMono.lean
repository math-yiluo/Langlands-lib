/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.CategoryTheory.SiteExtensionByZeroPresheaf

/-!
# Extension by zero for an arbitrary localized Grothendieck topology

Source: Stacks Project, Modules on Sites, Lemmas 03DI and 03DJ
(blueprint: new-over-pullback-adjunction-mono).

The presheaf hom-equivalence and injectivity arguments adapt the private helpers of
`SiteExtensionByZeroPresheafAdjoint` and `SiteExtensionByZeroExact`. Sheafification
then gives the result without the precoverage or pullback assumptions of those modules.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe u

namespace CategoryTheory

private abbrev sliceRestrict {C : Type u} [SmallCategory C] (W : C) :=
  (Functor.whiskeringLeft (Over W)ᵒᵖ Cᵒᵖ AddCommGrpCat.{u}).obj (Over.forget W).op

private noncomputable def sumLift {C : Type u} [SmallCategory C] (W : C)
    {F : (Over W)ᵒᵖ ⥤ AddCommGrpCat.{u}}
    {G : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (α : F ⟶ (sliceRestrict W).obj G) :
    (siteExtensionByZeroPresheaf W).obj F ⟶ G := by
  classical
  exact {
    app V := AddCommGrpCat.ofHom (DirectSum.toAddMonoid fun φ ↦
      (α.app (Opposite.op (Over.mk φ))).hom)
    naturality V V' a := by
      classical
      apply AddCommGrpCat.hom_ext
      dsimp [siteExtensionByZeroPresheaf, siteExtensionByZeroPresheafObj,
        siteExtensionByZeroRestrict, siteExtensionByZeroSection]
      apply DirectSum.addHom_ext
      intro φ x
      simp only [AddMonoidHom.comp_apply, DirectSum.toAddMonoid_of]
      exact ConcreteCategory.congr_hom (α.naturality
        (Opposite.op (Over.homMk a.unop : Over.mk (a.unop ≫ φ) ⟶ Over.mk φ))) x }

private noncomputable def sumRestrict {C : Type u} [SmallCategory C] (W : C)
    {F : (Over W)ᵒᵖ ⥤ AddCommGrpCat.{u}}
    {G : Cᵒᵖ ⥤ AddCommGrpCat.{u}}
    (β : (siteExtensionByZeroPresheaf W).obj F ⟶ G) :
    F ⟶ (sliceRestrict W).obj G := by
  classical
  exact {
    app Y := AddCommGrpCat.ofHom
      (DirectSum.of (fun φ : Y.unop.left ⟶ W ↦ F.obj (Opposite.op (Over.mk φ)))
        Y.unop.hom) ≫ β.app (Opposite.op Y.unop.left)
    naturality Y Y' a := by
      classical
      apply AddCommGrpCat.hom_ext
      ext x
      have h := ConcreteCategory.congr_hom (β.naturality ((Over.forget W).op.map a))
        (DirectSum.of (fun φ : Y.unop.left ⟶ W ↦ F.obj (Opposite.op (Over.mk φ)))
          Y.unop.hom x)
      dsimp [siteExtensionByZeroPresheaf, siteExtensionByZeroPresheafObj,
        siteExtensionByZeroRestrict, siteExtensionByZeroSection] at h
      simp only [AddMonoidHom.comp_apply, DirectSum.toAddMonoid_of] at h
      have aux (j : Y'.unop.left ⟶ W) (hj : j = Y'.unop.hom)
          (f : Over.mk j ⟶ Y.unop) (hf : f.left = a.unop.left) :
          DirectSum.of (fun φ ↦ F.obj (Opposite.op (Over.mk φ))) j
            ((F.map f.op).hom x) =
          DirectSum.of (fun φ ↦ F.obj (Opposite.op (Over.mk φ))) Y'.unop.hom
            ((F.map a).hom x) := by
        subst j
        have he : f = a.unop := Over.OverMorphism.ext hf
        subst f
        rfl
      have aux' := aux (a.unop.left ≫ Y.unop.hom) (Over.w a.unop)
        (Over.homMk a.unop.left : Over.mk (a.unop.left ≫ Y.unop.hom) ⟶ Y.unop) rfl
      erw [aux'] at h
      exact h }

private noncomputable def sumHomEquiv {C : Type u} [SmallCategory C] (W : C)
    (F : (Over W)ᵒᵖ ⥤ AddCommGrpCat.{u})
    (G : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    ((siteExtensionByZeroPresheaf W).obj F ⟶ G) ≃
      (F ⟶ (sliceRestrict W).obj G) where
  toFun := sumRestrict W
  invFun := sumLift W
  left_inv β := by
    classical
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.hom_ext
    apply DirectSum.addHom_ext
    intro φ x
    simp [sumLift, sumRestrict]
  right_inv α := by
    classical
    apply NatTrans.ext
    funext Y
    apply AddCommGrpCat.hom_ext
    ext x
    dsimp [sumLift, sumRestrict]
    erw [DirectSum.toAddMonoid_of]
    rfl

private noncomputable def sumAdjunction {C : Type u} [SmallCategory C] (W : C) :
    siteExtensionByZeroPresheaf W ⊣ sliceRestrict W :=
  Adjunction.mkOfHomEquiv {
    homEquiv := sumHomEquiv W
    homEquiv_naturality_left_symm := by
      intro F' F G α β
      classical
      apply NatTrans.ext
      funext V
      apply AddCommGrpCat.hom_ext
      apply DirectSum.addHom_ext
      intro φ x
      dsimp [sumHomEquiv, sumLift, siteExtensionByZeroPresheaf, siteExtensionByZeroHom,
        siteExtensionByZeroHomApp]
      erw [DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply, DirectSum.toAddMonoid_of]
      erw [AddMonoidHom.comp_apply, DirectSum.toAddMonoid_of]
    homEquiv_naturality_right := by
      intro F G G' α β
      apply NatTrans.ext
      funext Y
      simp [sumHomEquiv, sumRestrict, sliceRestrict, Category.assoc] }

end CategoryTheory
