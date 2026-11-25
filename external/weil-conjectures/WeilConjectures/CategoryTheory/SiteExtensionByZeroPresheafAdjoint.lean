/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.SiteExtensionByZeroPresheaf
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck

/-!
# Adjunction for extension by zero on a localized site

Source: literature/stacks-project/sites-modules.tex, Modules on Sites, Lemma 03DI
(blueprint: lem-weil-pbc-site-extension-by-zero-presheaf-adjoint).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction

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

/-- The sheafified direct-sum presheaf is left adjoint to restriction.

Source: literature/stacks-project/sites-modules.tex, Modules on Sites, Lemma 03DI
(blueprint: lem-weil-pbc-site-extension-by-zero-presheaf-adjoint).

Given a morphism `α : F ⟶ G|_W`, the first proof step defines a presheaf map by
sending the section in the `φ`-summand to `α.app (Over.mk φ)`. Naturality in the
slice gives compatibility with restrictions, and the direct-sum universal property
provides the unique map on each section. The second step factors this map uniquely
through sheafification. Conversely, composing a map from the sheafification with
the canonical presheaf map and restricting to each summand gives the inverse map.
The sheafification universal property proves that these constructions are inverse;
naturality in `F` and `G` follows componentwise. The displayed hom-set
bijections are represented by the hom-equivalences of the resulting adjunction.
-/
theorem siteExtensionByZeroPresheaf_adjunction
    {C : Type u} [SmallCategory C]
    (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (W : C) :
    ∃ e : siteExtensionByZeroSheaf J W ⊣
        (Over.forget W).sheafPushforwardContinuous AddCommGrpCat.{u}
          (J.toGrothendieck.over W) J.toGrothendieck,
      ∀ (F : Sheaf (J.toGrothendieck.over W) AddCommGrpCat.{u})
        (G : Sheaf J.toGrothendieck AddCommGrpCat.{u}),
        ∀ (α : F ⟶
          ((Over.forget W).sheafPushforwardContinuous AddCommGrpCat.{u}
            (J.toGrothendieck.over W) J.toGrothendieck).obj G),
          e.homEquiv F G ((e.homEquiv F G).symm α) = α := by
  let e : siteExtensionByZeroSheaf J W ⊣
      (Over.forget W).sheafPushforwardContinuous AddCommGrpCat.{u}
        (J.toGrothendieck.over W) J.toGrothendieck :=
    ((sumAdjunction W).comp
      (sheafificationAdjunction J.toGrothendieck AddCommGrpCat.{u})).restrictFullyFaithful
        (fullyFaithfulSheafToPresheaf (J.toGrothendieck.over W) AddCommGrpCat.{u})
        (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)
  refine ⟨e, ?_⟩
  intro F G α
  exact (e.homEquiv F G).apply_symm_apply α

end CategoryTheory
