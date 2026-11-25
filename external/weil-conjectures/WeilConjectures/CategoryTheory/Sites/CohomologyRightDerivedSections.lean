/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Adjunction.Whiskering
import WeilConjectures.CategoryTheory.Abelian.ExtRightDerivedHom

/-!
# Object cohomology as derived sections

Source: Stacks Project, Cohomology on Sites, Section 01FT.
(blueprint: lem-sc-site-cohomology-right-derived-sections).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

private noncomputable def freeSectionsEquiv
    {C : Type u} [SmallCategory C] (U : C) (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (yoneda.obj U ⋙ AddCommGrpCat.free ⟶ F) ≃+ F.obj (op U) where
  toEquiv := ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _).trans yonedaEquiv
  map_add' a b := by
    change ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _ (a + b)).app
      (op U) (𝟙 U) = _
    simp only [Adjunction.homEquiv_apply, NatTrans.comp_app,
      Adjunction.whiskerRight_unit_app_app]
    rfl

private noncomputable def sectionsEquiv
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] (U : C) (F : Sheaf J AddCommGrpCat.{u}) :
    ((presheafToSheaf J AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ F) ≃+ F.obj.obj (op U) :=
  ((sheafificationAdjunction J AddCommGrpCat.{u}).homAddEquiv _ F).trans
    (freeSectionsEquiv U F.obj)

private lemma sectionsEquiv_naturality
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] (U : C)
    {F G : Sheaf J AddCommGrpCat.{u}} (f : F ⟶ G)
    (a : (presheafToSheaf J AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ F) :
    sectionsEquiv J U G (a ≫ f) = f.hom.app (op U) (sectionsEquiv J U F a) := by
  dsimp only [sectionsEquiv, AddEquiv.trans_apply, Adjunction.homAddEquiv_apply]
  rw [Adjunction.homEquiv_naturality_right]
  dsimp [freeSectionsEquiv]
  rfl

private noncomputable def sectionsIso
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}] (U : C) :
    preadditiveCoyoneda.obj (op ((presheafToSheaf J AddCommGrpCat.{u}).obj
      (yoneda.obj U ⋙ AddCommGrpCat.free))) ≅
      sheafToPresheaf J AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U) :=
  NatIso.ofComponents (fun F ↦ (sectionsEquiv J U F).toAddCommGrpIso) (by
    intro F G f
    ext a
    exact sectionsEquiv_naturality J U f a)

/-- Ext cohomology over an object agrees naturally with the right derived sections functor.
Source: Stacks Project, Cohomology on Sites, Section 01FT; the convention in
`def-weil-pbc-sites-and-cohomology`.
(blueprint: lem-sc-site-cohomology-right-derived-sections).

Proof: the free abelian sheaf on the representable of `U` represents sections over `U`.
Indeed, sheafification adjunction, the free-abelian/forgetful adjunction, and Yoneda
identify morphisms from this sheaf to `F` with `F(U)`, naturally and additively in `F`.
Apply these identifications degreewise to an injective resolution of `F`. Ext from the
representing sheaf is the cohomology of its Hom complex, which is consequently the
complex of sections of the resolution. This computes the right derived sections.
Comparison maps lifting morphisms of sheaves commute with the degreewise identification;
homotopic comparison maps induce equal maps on cohomology. The resulting isomorphisms
are therefore natural in `F`, giving the displayed natural isomorphism in every degree.
No compactness or nonemptiness of `U` is required. -/
theorem nonempty_cohomologyPresheafFunctor_eval_iso_rightDerived
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
    (U : C) (q : ℕ) :
    Nonempty ((cohomologyPresheafFunctor J q ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)) ≅
      (sheafToPresheaf J AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q) := by
  let X := (presheafToSheaf J AddCommGrpCat.{u}).obj
    (yoneda.obj U ⋙ AddCommGrpCat.free)
  obtain ⟨e⟩ := nonempty_extFunctor_iso_rightDerivedHom X q
  let s := sectionsIso J U
  let d : (preadditiveCoyoneda.obj (op X)).rightDerived q ≅
      (sheafToPresheaf J AddCommGrpCat.{u} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)).rightDerived q :=
    { hom := NatTrans.rightDerived s.hom q
      inv := NatTrans.rightDerived s.inv q
      hom_inv_id := by rw [← NatTrans.rightDerived_comp, s.hom_inv_id,
        NatTrans.rightDerived_id]
      inv_hom_id := by rw [← NatTrans.rightDerived_comp, s.inv_hom_id,
        NatTrans.rightDerived_id] }
  exact ⟨(show (cohomologyPresheafFunctor J q ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)) ≅
      (Abelian.extFunctor q).obj (op X) from Iso.refl _) ≪≫ e ≪≫ d⟩

end CategoryTheory.Sheaf

