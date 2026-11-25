/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData
public import WeilConjectures.AlgebraicGeometry.DirectImageSquareUnitTransport
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageSquareMate
/-! # Complex localization of the normalized direct-image square

## References

* Stacks Project, Tags 08HY and 0D5T
-/

@[expose] public section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
omit [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] in
private theorem square_paste {C : Type*} [Category C]
    {A₁ A₂ B₁ B₂ P Q : C} (c₁ : A₁ ≅ B₁) (c₂ : A₂ ≅ B₂)
    (u₁ : P ⟶ A₁) (u₂ : Q ⟶ A₂) (b₁ : P ⟶ B₁) (b₂ : Q ⟶ B₂)
    (d : A₁ ⟶ A₂) (e : P ⟶ Q) (δ : B₁ ⟶ B₂)
    (h₁ : u₁ ≫ c₁.hom = b₁) (h₂ : u₂ ≫ c₂.hom = b₂)
    (hδ : δ = c₁.inv ≫ d ≫ c₂.hom) (he : u₁ ≫ d = e ≫ u₂) :
    b₁ ≫ δ = e ≫ b₂ := by
  rw [← h₁, hδ]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, he, Category.assoc, h₂]

attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit

-- Comparing the composite pushforward objects requires extra elaboration.
private theorem normalized_unit {A B C : Scheme.{u}} (s : A ⟶ B) (t : B ⟶ C)
    (J : HomotopyCategory (SheafOfModules.{u} (moduleRings A.toRingedSpace)) (.up ℤ)) :
    (RingedSpace.moduleDirectImage (s ≫ t).toLRSHom.toShHom).rightDerivedFunctorUnit.app J ≫
      (schemeNormalizedDirectImageCompIso s t).inv.app (DerivedCategory.Qh.obj J) =
    (RingedSpace.moduleDirectImage t.toLRSHom.toShHom).rightDerivedFunctorUnit.app
      (((RingedSpace.moduleDirectImage s.toLRSHom.toShHom).mapHomotopyCategory (.up ℤ)).obj J) ≫
    (schemeDerivedDirectImage t).map
      ((RingedSpace.moduleDirectImage s.toLRSHom.toShHom).rightDerivedFunctorUnit.app J) := by
  exact (Classical.choose_spec (RingedSpace.exists_derivedModuleDirectImageComposition
    s.toLRSHom.toShHom t.toLRSHom.toShHom)) J

attribute [local irreducible] schemeNormalizedDirectImageCompIso

set_option linter.all false in
private theorem general_square_unit
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g)
    (J : HomotopyCategory (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) (.up ℤ)) :
    let κ := relativeMVComp f' g ≪≫
      eqToIso (congrArg (fun t ↦ derivedPullback.{u, w} t) h.symm) ≪≫ (relativeMVComp g' f).symm
    let δ := conjugateEquiv ((relativeMVAdj f).comp (relativeMVAdj g'))
      ((relativeMVAdj g).comp (relativeMVAdj f')) κ.hom
    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app
      (((RingedSpace.moduleDirectImage g'.toLRSHom.toShHom).mapHomotopyCategory
        (.up ℤ)).obj J) ≫
      (schemeDerivedDirectImage f).map
        ((RingedSpace.moduleDirectImage g'.toLRSHom.toShHom).rightDerivedFunctorUnit.app J) ≫
      δ.app (DerivedCategory.Qh.obj J) =
    DerivedCategory.Qh.map
        (((directImageSquareIso g' f f' g h).hom.mapHomotopyCategory (.up ℤ)).app J) ≫
      (RingedSpace.moduleDirectImage g.toLRSHom.toShHom).rightDerivedFunctorUnit.app
        (((RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).mapHomotopyCategory
          (.up ℤ)).obj J) ≫
      (schemeDerivedDirectImage g).map
        ((RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).rightDerivedFunctorUnit.app J)
      := by
  intro κ δ
  have hc₁ := normalized_unit g' f J
  have hc₂ := normalized_unit f' g J
  have he := directImageSquare_unit_transport g' f f' g h J
  have hd := derivedDirectImage_square_mate f f' g g' h
  have hd' := congrArg (fun τ ↦ τ.app (DerivedCategory.Qh.obj J)) hd
  simp only [NatTrans.comp_app] at hd'
  rw [← Category.assoc]
  exact square_paste (C := schemeDerivedCategory.{u, w} S)
    ((schemeNormalizedDirectImageCompIso g' f).app (DerivedCategory.Qh.obj J)).symm
    ((schemeNormalizedDirectImageCompIso f' g).app (DerivedCategory.Qh.obj J)).symm
    _ _ _ _ _ _ _ hc₁ hc₂ hd' he

set_option linter.all false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma localization_unit_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    (schemeMVDirectImageLocalization f).app I =
      (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj I) := by
  dsimp only [schemeMVDirectImageLocalization, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.mapHomotopyCategoryFactors, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_inv, Quotient.lift.isLift_hom]
  dsimp +instances [DerivedCategory, DerivedCategory.Q, DerivedCategory.Qh,
    schemeDerivedDirectImage, RingedSpace.derivedModuleDirectImage,
    instCategoryDerivedCategory]
  erw [HomologicalComplexUpToQuasiIso.Qh.map_id,
    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctor.map_id]
  simp only [Category.id_comp, Category.comp_id]

set_option linter.all false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Localization of an ordinary direct-image square gives the square mate of
pinned derived pullbacks on every complex. -/
theorem relativeMV_direct_image_square_localization
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g)
    (J : CochainComplex (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) ℤ) :
    let κ := relativeMVComp f' g ≪≫
      eqToIso (congrArg (fun t ↦ derivedPullback.{u, w} t) h.symm) ≪≫
      (relativeMVComp g' f).symm
    let δ := conjugateEquiv ((relativeMVAdj f).comp (relativeMVAdj g'))
      ((relativeMVAdj g).comp (relativeMVAdj f')) κ.hom
    let c := Functor.mapHomologicalComplexCompIso
        (directImageSquareIso g' f f' g h) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom ⋙
          RingedSpace.moduleDirectImage g.toLRSHom.toShHom)) (.up ℤ)).symm
    (schemeMVDirectImageLocalization f).app
        (((RingedSpace.moduleDirectImage g'.toLRSHom.toShHom).mapHomologicalComplex
          (.up ℤ)).obj J) ≫
      (schemeDerivedDirectImage f).map ((schemeMVDirectImageLocalization g').app J) ≫
      δ.app (DerivedCategory.Q.obj J) =
    DerivedCategory.Q.map (c.hom.app J) ≫
      (schemeMVDirectImageLocalization g).app
        (((RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).mapHomologicalComplex
          (.up ℤ)).obj J) ≫
      (schemeDerivedDirectImage g).map ((schemeMVDirectImageLocalization f').app J) := by
  extract_lets κ δ c
  rw [localization_unit_eq, localization_unit_eq, localization_unit_eq,
    localization_unit_eq]
  have hn := general_square_unit f f' g g' h ((HomotopyCategory.quotient _ (.up ℤ)).obj J)
  simpa +instances only [c, δ, κ, Quotient.functor, CategoryTheory.Quotient.lift,
    Functor.mapHomologicalComplexCompIso,
    Functor.mapHomotopyCategory, HomologicalComplexUpToQuasiIso.Qh,
    HomotopyCategory.quotient, HomotopyCategory.quotient_obj_as,
    Quotient.lift_obj_functor_obj,
    Quotient.lift_map_functor_map, Iso.refl_inv, NatTrans.mapHomologicalComplex_id,
    NatTrans.id_app, Functor.comp_obj,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, NatTrans.comp_app,
    NatIso.mapHomologicalComplex, NatTrans.mapHomotopyCategory,
    Quotient.natTransLift, Functor.whiskerRight_app, DerivedCategory.Qh, DerivedCategory.Q,
    DerivedCategory, instCategoryDerivedCategory, Functor.map_comp,
    Functor.map_id, Category.comp_id] using hn

end AlgebraicGeometry
