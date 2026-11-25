/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap

/-! # Augmentation square for degree zero resolution maps

Source: Stacks Project, Tags 01F8, 01F9 and 01FB
(blueprint: lem-weil-pbc-module-cohomology-fmap-zero-augmentation).
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

private theorem forget_homologyπ {R : Type u} [Ring R]
    (S : ShortComplex (ModuleCat.{u} R)) :
    (forget₂ _ AddCommGrpCat.{u}).map S.homologyπ ≫
        (S.mapHomologyIso (forget₂ _ AddCommGrpCat.{u})).inv =
      (S.mapCyclesIso (forget₂ _ AddCommGrpCat.{u})).inv ≫
        (S.map (forget₂ _ AddCommGrpCat.{u})).homologyπ := by
  let U := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  let hl := S.homologyData.left
  rw [hl.mapHomologyIso_eq U, hl.mapCyclesIso_eq U]
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc]
  rw [← U.map_comp_assoc, hl.homologyπ_comp_homologyIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  erw [(hl.map U).π_comp_homologyIso_inv]

set_option backward.isDefEq.respectTransparency false in
private theorem forget_augmentation {C : Type*} [Category* C] [Abelian C]
    [HasInjectiveResolutions C] {R : Type u} [Ring R]
    (Γ : C ⥤ ModuleCat.{u} R) [Γ.Additive] {F : C} (I : InjectiveResolution F) :
    (forget₂ _ AddCommGrpCat.{u}).map (Γ.toRightDerivedZero.app F) ≫
      (forget₂ _ AddCommGrpCat.{u}).map (I.isoRightDerivedObj Γ 0).hom ≫
      ((((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc 0).mapHomologyIso
        (forget₂ _ AddCommGrpCat.{u})).inv =
    I.toRightDerivedZero' (Γ ⋙ forget₂ _ AddCommGrpCat.{u}) ≫
      HomologicalComplex.homologyπ _ 0 := by
  let U := forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}
  rw [I.toRightDerivedZero_eq Γ]
  simp only [Functor.map_comp, Category.assoc]
  rw [← U.map_comp_assoc (I.isoRightDerivedObj Γ 0).inv,
    Iso.inv_hom_id, U.map_id, Category.id_comp]
  change U.map (I.toRightDerivedZero' Γ) ≫
    U.map (((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homologyπ 0) ≫
      ((((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc 0).mapHomologyIso
        U).inv = _
  erw [forget_homologyπ]
  rw [← Category.assoc]
  congr 1
  apply (cancel_mono
    (((((Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc 0).map U).iCycles)).1
  rw [Category.assoc, ← ShortComplex.mapCyclesIso_hom_iCycles]
  dsimp only [U]
  rw [Iso.inv_hom_id_assoc, ShortComplex.mapCyclesIso_hom_iCycles]
  change U.map (I.toRightDerivedZero' Γ) ≫
    U.map (HomologicalComplex.iCycles _ 0) =
      I.toRightDerivedZero' (Γ ⋙ U) ≫ HomologicalComplex.iCycles _ 0
  rw [← U.map_comp, InjectiveResolution.toRightDerivedZero'_comp_iCycles,
    InjectiveResolution.toRightDerivedZero'_comp_iCycles]
  rfl

-- Cancel abstract isomorphisms without unfolding the concrete resolution comparisons.
private theorem augmentation_diagram_cancel {C : Type*} [Category* C]
    {A B C₁ D E F K L : C} (rJ : B ≅ C₁) (sJ : D ≅ C₁)
    (rI : E ≅ F) (sI : K ≅ F) (aJ : A ⟶ B) (aI : A ⟶ E)
    (b : D ⟶ L) (m : K ⟶ L) [IsIso m]
    (h : aJ ≫ rJ.hom ≫ sJ.inv ≫ b = aI ≫ rI.hom ≫ sI.inv ≫ m) :
    aJ ≫ rJ.hom ≫ sJ.inv ≫ b ≫ inv m ≫ sI.hom ≫ rI.inv = aI := by
  apply (cancel_mono rI.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_mono sI.inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply (cancel_mono m).1
  simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using h

-- Comparing the module and abelian-group homology models needs extra elaboration work.
set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero resolution formula commutes with the canonical augmentations.
Source: Stacks Project, Cohomology of Sheaves, Remark 01FB, equation-choice;
Mathlib CategoryTheory.Abelian.RightDerived, toRightDerivedZero_eq
(blueprint: lem-weil-pbc-module-cohomology-fmap-zero-augmentation).

Proof: express each toRightDerivedZero using its resolution by
InjectiveResolution.toRightDerivedZero_eq. Before the inverse vertical map is
applied, both routes send a section s of G to the zero-cycle represented by
β⁰(s_J(s)): D.compatible identifies this with lambda⁰(h_*s_I(φ(s))).
The comparison D.a.inv is the canonical restriction along h⁻¹(Y) = X by
D.sections, so it identifies the latter section with s_I(φ_Y(s)) on X.
Naturality of cyclesMap and homologyπ transfers the augmentation equation to
H⁰. The vertical homology map is invertible by D.invertible; compose with its
inverse and cancel. Finally cancel the two resolution comparison isomorphisms.
The result is the stated augmentation square; left exactness is only needed
later to invert its two augmentation maps. -/
theorem ModuleCohomologyFMapData.map_zero_augmentation {X Y : Scheme.{u}} {h : X ⟶ Y}
    {G : SheafOfModules.{u} Y.ringCatSheaf} {F : SheafOfModules.{u} X.ringCatSheaf}
    {φ : G ⟶ (pushforward h).obj F} (D : ModuleCohomologyFMapData h G F φ) :
    (forget₂ _ AddCommGrpCat.{u}).map
        ((RingedSpace.globalSectionsFunctor Y.toRingedSpace).toRightDerivedZero.app G) ≫
      D.map 0 =
    (forget₂ _ AddCommGrpCat.{u}).map
        ((RingedSpace.globalSectionsFunctor Y.toRingedSpace).map φ) ≫
      (forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
      AddCommGrpCat.{u}).map
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app F) :=
  by
    let ΓX := RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{u}
    let ΓY := RingedSpace.globalSectionsFunctor Y.toRingedSpace ⋙
      forget₂ _ AddCommGrpCat.{u}
    let b := (ΓY.mapHomologicalComplex (ComplexShape.up ℕ)).map D.β
    let μ := D.a.hom ≫ (ΓY.mapHomologicalComplex (ComplexShape.up ℕ)).map D.lambda
    have ha : D.a.inv.f 0 = 𝟙 _ := by
      rw [D.sections]
      simp only [eqToHom_refl, op_id]
      erw [(presheaf (D.I.cocomplex.X 0)).map_id]
      rfl
    have ha' : D.a.hom.f 0 = 𝟙 _ := by
      have w := congrArg (fun f ↦ f.f 0) D.a.hom_inv_id
      change D.a.hom.f 0 ≫ D.a.inv.f 0 = 𝟙 _ at w
      rw [ha, Category.comp_id] at w
      exact w
    have hc : D.J.toRightDerivedZero' ΓY ≫ HomologicalComplex.cyclesMap b 0 =
        ΓY.map φ ≫ D.I.toRightDerivedZero' ΓX ≫
          HomologicalComplex.cyclesMap μ 0 := by
      apply (cancel_mono (HomologicalComplex.iCycles _ 0)).1
      simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
        InjectiveResolution.toRightDerivedZero'_comp_iCycles_assoc]
      dsimp only [b, μ, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
      rw [ha', Category.id_comp]
      rw [InjectiveResolution.toRightDerivedZero'_comp_iCycles_assoc]
      change ΓY.map (D.J.ι.f 0) ≫ ΓY.map (D.β.f 0) =
        ΓY.map φ ≫ ΓX.map (D.I.ι.f 0) ≫ ΓY.map (D.lambda.f 0)
      rw [← ΓY.map_comp, D.compatible]
      simp only [CategoryTheory.Functor.map_comp]
      rfl
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) 0
    have hh : D.J.toRightDerivedZero' ΓY ≫ HomologicalComplex.homologyπ _ 0 ≫ H.map b =
        ΓY.map φ ≫ D.I.toRightDerivedZero' ΓX ≫
          HomologicalComplex.homologyπ _ 0 ≫ H.map μ := by
      dsimp only [H, HomologicalComplex.homologyFunctor]
      simpa only [Category.assoc, HomologicalComplex.homologyπ_naturality] using
        congrArg (fun f ↦ f ≫ HomologicalComplex.homologyπ _ 0) hc
    let UX := forget₂
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat.{u}
    let UY := forget₂
      (ModuleCat.{u} ((moduleRings Y.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat.{u}
    have : IsIso (H.map μ) := D.invertible 0
    dsimp only [ModuleCohomologyFMapData.map]
    refine augmentation_diagram_cancel
      (UY.mapIso (D.J.isoRightDerivedObj
        (RingedSpace.globalSectionsFunctor Y.toRingedSpace) 0))
      (((RingedSpace.globalSectionsComplex D.J).sc 0).mapHomologyIso UY)
      (UX.mapIso (D.I.isoRightDerivedObj
        (RingedSpace.globalSectionsFunctor X.toRingedSpace) 0))
      (((RingedSpace.globalSectionsComplex D.I).sc 0).mapHomologyIso UX)
      _ _ (H.map b) (H.map μ) ?_
    dsimp only [Functor.mapIso_hom]
    simp only [Category.assoc]
    erw [reassoc_of% (forget_augmentation
        (RingedSpace.globalSectionsFunctor Y.toRingedSpace) D.J),
      reassoc_of% (forget_augmentation
        (RingedSpace.globalSectionsFunctor X.toRingedSpace) D.I)]
    exact hh

end AlgebraicGeometry.Scheme.Modules
