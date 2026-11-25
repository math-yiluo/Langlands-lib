/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GlobalHomAdjunctionIso
public import WeilConjectures.AlgebraicGeometry.DerivedDirectImageSquareMate

/-! # Left path of the normalized mixed Leray unit diagram
Source: Stacks Project, Cohomology, Tags 0D5T and 0D5W.
(blueprint: lem-sc-mixed-sections-left-unit-normalization).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w wA
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

-- Keep the derived functors abstract while pasting units. The explicit source
-- equality transports the first Leray equation without unfolding localization choices.
private theorem generic_first_layer
    {C D E A B : Type*} [Category C] [Category D] [Category E] [Category A] [Category B]
    [Abelian C] [Abelian D] [Abelian E] [Abelian A] [Abelian B]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    (HY : D ⥤ A) (HZ : E ⥤ B) (S : A ⥤ B)
    [F.Additive] [G.Additive] [H.Additive] [HY.Additive] [HZ.Additive] [S.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (hcomp : H = F ⋙ G)
    (e : F.rightDerivedFunctor ⋙ G.rightDerivedFunctor ≅ H.rightDerivedFunctor)
    (c : G.rightDerivedFunctor ⋙ HZ.rightDerivedFunctor ≅
      HY.rightDerivedFunctor ⋙ S.mapDerivedCategory)
    (K : HomotopyCategory C (.up ℤ))
    (he : HEq (H.rightDerivedFunctorUnit.app K ≫ e.inv.app (DerivedCategory.Qh.obj K))
      (G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
        G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app K)))
    (hA : DerivedCategory.Qh.obj ((HZ.mapHomotopyCategory (.up ℤ)).obj
        ((G.mapHomotopyCategory (.up ℤ)).obj ((F.mapHomotopyCategory (.up ℤ)).obj K))) =
      (S.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).obj
        ((HY.mapHomotopyCategory (.up ℤ)).obj ((F.mapHomotopyCategory (.up ℤ)).obj K)))
    (hg : HEq (HZ.rightDerivedFunctorUnit.app
          ((G.mapHomotopyCategory (.up ℤ)).obj ((F.mapHomotopyCategory (.up ℤ)).obj K)) ≫
        HZ.rightDerivedFunctor.map
          (G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj K)) ≫
        c.hom.app (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj K)))
      (S.mapDerivedCategoryFactorsh.inv.app
          ((HY.mapHomotopyCategory (.up ℤ)).obj ((F.mapHomotopyCategory (.up ℤ)).obj K)) ≫
        S.mapDerivedCategory.map
          (HY.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj K)))) :
    HEq (HZ.rightDerivedFunctorUnit.app ((H.mapHomotopyCategory (.up ℤ)).obj K) ≫
      HZ.rightDerivedFunctor.map (H.rightDerivedFunctorUnit.app K) ≫
      HZ.rightDerivedFunctor.map (e.inv.app (DerivedCategory.Qh.obj K)) ≫
      c.hom.app (F.rightDerivedFunctor.obj (DerivedCategory.Qh.obj K)))
    (S.mapDerivedCategoryFactorsh.inv.app
        ((HY.mapHomotopyCategory (.up ℤ)).obj ((F.mapHomotopyCategory (.up ℤ)).obj K)) ≫
      S.mapDerivedCategory.map
        (HY.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj K)) ≫
      S.mapDerivedCategory.map (HY.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app K))) := by
  subst H
  have he' := eq_of_heq he
  have hp : HZ.rightDerivedFunctorUnit.app
        (((F ⋙ G).mapHomotopyCategory (.up ℤ)).obj K) ≫
      HZ.rightDerivedFunctor.map ((F ⋙ G).rightDerivedFunctorUnit.app K) ≫
      HZ.rightDerivedFunctor.map (e.inv.app (DerivedCategory.Qh.obj K)) ≫
      c.hom.app (F.rightDerivedFunctor.obj (DerivedCategory.Qh.obj K)) =
    (HZ.rightDerivedFunctorUnit.app
        ((G.mapHomotopyCategory (.up ℤ)).obj ((F.mapHomotopyCategory (.up ℤ)).obj K)) ≫
      HZ.rightDerivedFunctor.map
        (G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj K)) ≫
      c.hom.app (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj K))) ≫
    S.mapDerivedCategory.map (HY.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app K)) := by
    calc
      _ = HZ.rightDerivedFunctorUnit.app
          (((F ⋙ G).mapHomotopyCategory (.up ℤ)).obj K) ≫
          HZ.rightDerivedFunctor.map
            ((F ⋙ G).rightDerivedFunctorUnit.app K ≫
              e.inv.app (DerivedCategory.Qh.obj K)) ≫
          c.hom.app (F.rightDerivedFunctor.obj (DerivedCategory.Qh.obj K)) := by
        simp only [Functor.map_comp, Category.assoc]
      _ = HZ.rightDerivedFunctorUnit.app
          (((F ⋙ G).mapHomotopyCategory (.up ℤ)).obj K) ≫
          HZ.rightDerivedFunctor.map
            (G.rightDerivedFunctorUnit.app ((F.mapHomotopyCategory (.up ℤ)).obj K) ≫
              G.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app K)) ≫
          c.hom.app (F.rightDerivedFunctor.obj (DerivedCategory.Qh.obj K)) := by rw [he']
      _ = _ := by
        simp only [Functor.map_comp, Category.assoc]
        have hn := c.hom.naturality (F.rightDerivedFunctorUnit.app K)
        simp only [Functor.comp_map] at hn
        erw [hn]
        rfl
  have hfinish := CategoryTheory.heq_comp hA rfl rfl hg
    (HEq.refl (S.mapDerivedCategory.map
      (HY.rightDerivedFunctor.map (F.rightDerivedFunctorUnit.app K))))
  apply (heq_of_eq hp).trans
  simpa only [Category.assoc] using hfinish


private theorem finish_unit_paste {C D : Type*} [Category C] [Category D]
    (S : C ⥤ D) {A : D} {B E F G J : C} {T : D}
    (p : A ⟶ T) (c : T ⟶ S.obj F) (b : A ⟶ S.obj B)
    (u : B ⟶ E) (v : E ⟶ F) (t : F ⟶ G) (d : B ⟶ J) (q : J ⟶ G)
    (hg : p ≫ c = b ≫ S.map u ≫ S.map v)
    (hf : u ≫ v ≫ t = d ≫ q) :
    p ≫ c ≫ S.map t = b ≫ S.map d ≫ S.map q := by
  rw [← Category.assoc, hg]
  simp only [Category.assoc]
  rw [← S.map_comp, ← S.map_comp, hf, S.map_comp]

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]

private theorem mixedSections_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : HomotopyCategory
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    (RingedSpace.globalSectionsFunctor Y.toRingedSpace).rightDerivedFunctorUnit.app
        (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategory
          (.up ℤ)).obj K) ≫
      (schemeDerivedGlobalSections Y).map
        ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app K) ≫
      (mixedGlobalSectionsDirectImageIso f).hom.app (DerivedCategory.Qh.obj K) =
    (ModuleCat.restrictScalars.{u}
      (R := (moduleRings Y.toRingedSpace).obj.obj (op ⊤))
      (S := (moduleRings X.toRingedSpace).obj.obj (op ⊤))
      f.appTop.hom).mapDerivedCategoryFactorsh.inv.app
        (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomotopyCategory (.up ℤ)).obj K) ≫
      (schemeGlobalScalarRestriction f).map
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctorUnit.app K) := by
  have hc : Classical.choose (exists_mixedGlobalSectionsDirectImageIso f) = Iso.refl _ := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply ModuleCat.hom_ext
    ext x
    exact (Classical.choose_spec
      (Classical.choose_spec (exists_mixedGlobalSectionsDirectImageIso f))).1 M x
  have h := (Classical.choose_spec
    (Classical.choose_spec (exists_mixedGlobalSectionsDirectImageIso f))).2 K
  change _ ≫ _ ≫ (mixedGlobalSectionsDirectImageIso f).hom.app _ = _ at h
  rw [hc] at h
  erw [Iso.refl_symm, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp] at h
  exact h

-- Give the generic paste lemma the heterogeneous equations with their exact source types.
omit [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)] in
private theorem mixedSections_composition_unit_heq
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    let Df := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let Dg := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
    let Dfg := RingedSpace.moduleDirectImage (f ≫ g).toLRSHom.toShHom
    HEq (Dfg.rightDerivedFunctorUnit.app K ≫
      (schemeNormalizedDirectImageCompIso f g).inv.app (DerivedCategory.Qh.obj K))
      (Dg.rightDerivedFunctorUnit.app ((Df.mapHomotopyCategory (.up ℤ)).obj K) ≫
        Dg.rightDerivedFunctor.map (Df.rightDerivedFunctorUnit.app K)) := by
  dsimp only
  have he := (Classical.choose_spec
    (@RingedSpace.exists_derivedModuleDirectImageComposition.{u, w, w, w}
      X.toRingedSpace Y.toRingedSpace Z.toRingedSpace
      (‹∀ Z : Scheme.{u}, HasDerivedCategory.{w}
        (SheafOfModules.{u} (moduleRings Z.toRingedSpace))› X)
      (‹∀ Z : Scheme.{u}, HasDerivedCategory.{w}
        (SheafOfModules.{u} (moduleRings Z.toRingedSpace))› Y)
      (‹∀ Z : Scheme.{u}, HasDerivedCategory.{w}
        (SheafOfModules.{u} (moduleRings Z.toRingedSpace))› Z)
      f.toLRSHom.toShHom g.toLRSHom.toShHom)) K
  exact heq_of_eq he

omit [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] in
private theorem mixedSections_global_source {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)) :
    DerivedCategory.Qh.obj
        (((RingedSpace.globalSectionsFunctor Z.toRingedSpace).mapHomotopyCategory (.up ℤ)).obj
          (((RingedSpace.moduleDirectImage g.toLRSHom.toShHom).mapHomotopyCategory
            (.up ℤ)).obj K)) =
      ((ModuleCat.restrictScalars.{u}
        (R := (moduleRings Z.toRingedSpace).obj.obj (op ⊤))
        (S := (moduleRings Y.toRingedSpace).obj.obj (op ⊤)) g.appTop.hom).mapHomotopyCategory
          (.up ℤ) ⋙ DerivedCategory.Qh).obj
        (((RingedSpace.globalSectionsFunctor Y.toRingedSpace).mapHomotopyCategory
          (.up ℤ)).obj K) := by
  rfl

private theorem mixedSections_unit_heq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : HomotopyCategory
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    HEq ((RingedSpace.globalSectionsFunctor Y.toRingedSpace).rightDerivedFunctorUnit.app
        (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategory
          (.up ℤ)).obj K) ≫
      (schemeDerivedGlobalSections Y).map
        ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app K) ≫
      (mixedGlobalSectionsDirectImageIso f).hom.app (DerivedCategory.Qh.obj K))
    ((ModuleCat.restrictScalars.{u}
      (R := (moduleRings Y.toRingedSpace).obj.obj (op ⊤))
      (S := (moduleRings X.toRingedSpace).obj.obj (op ⊤))
      f.appTop.hom).mapDerivedCategoryFactorsh.inv.app
        (((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomotopyCategory (.up ℤ)).obj K) ≫
      (schemeGlobalScalarRestriction f).map
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctorUnit.app K)) := by
  exact heq_of_eq (mixedSections_unit f K)

/-- The left path becomes the iterated scalar-factor path before any unit cancellation.
Source: Stacks Project, Cohomology, Tags 0D5T and 0D5W; the pinned-unit calculation
in lem-sc-mixed-sections-composition-kinjective.
(blueprint: lem-sc-mixed-sections-left-unit-normalization).

Proof: Expand p using the normalized direct-image composition equation:
unit_Dfg followed by e.inv equals unit_Dg at Df(K), followed by RDg(unit_Df).
Naturality of c_g at unit_Df moves RDg(unit_Df) across c_g. Apply the mixed Leray
unit equation for g at Df(K). The two remaining maps inside Sg combine, by
functoriality, with the global-sections unit on Y. Apply the mixed Leray unit
equation for f at K. Distribute Sg over this composite to obtain b. The underived
Leray comparisons are identity on sections; their homotopy composition maps
cancel with their inverses. No unit is canceled, and I need not be K-injective.
For identity maps, zero complexes, and empty schemes the same equations hold;
no nonemptiness, boundedness, flatness, or preservation of K-injectivity is used.
The sheaf and module localization universes remain independent. -/
theorem mixedSections_left_unit_normalization
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let K := (HomotopyCategory.quotient _ (.up ℤ)).obj I
    let F := DerivedCategory.Qh.obj K
    let Df := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let Dfg := RingedSpace.moduleDirectImage (f ≫ g).toLRSHom.toShHom
    let HX := RingedSpace.globalSectionsFunctor X.toRingedSpace
    let HY := RingedSpace.globalSectionsFunctor Y.toRingedSpace
    let HZ := RingedSpace.globalSectionsFunctor Z.toRingedSpace
    let Sf := ModuleCat.restrictScalars.{u}
      (R := (moduleRings Y.toRingedSpace).obj.obj (op ⊤))
      (S := (moduleRings X.toRingedSpace).obj.obj (op ⊤)) f.appTop.hom
    let Sg := ModuleCat.restrictScalars.{u}
      (R := (moduleRings Z.toRingedSpace).obj.obj (op ⊤))
      (S := (moduleRings Y.toRingedSpace).obj.obj (op ⊤)) g.appTop.hom
    let e := schemeNormalizedDirectImageCompIso f g
    let p := HZ.rightDerivedFunctorUnit.app ((Dfg.mapHomotopyCategory (.up ℤ)).obj K) ≫
      (schemeDerivedGlobalSections Z).map (Dfg.rightDerivedFunctorUnit.app K) ≫
      (schemeDerivedGlobalSections Z).map (e.inv.app F)
    let b := Sg.mapDerivedCategoryFactorsh.inv.app
        ((HY.mapHomotopyCategory (.up ℤ)).obj ((Df.mapHomotopyCategory (.up ℤ)).obj K)) ≫
      (schemeGlobalScalarRestriction g).map
        (Sf.mapDerivedCategoryFactorsh.inv.app ((HX.mapHomotopyCategory (.up ℤ)).obj K)) ≫
      (schemeGlobalScalarRestriction g).map
        ((schemeGlobalScalarRestriction f).map (HX.rightDerivedFunctorUnit.app K))
    p ≫ (mixedGlobalSectionsDirectImageIso g).hom.app
        ((schemeDerivedDirectImage f).obj F) ≫
      (schemeGlobalScalarRestriction g).map
        ((mixedGlobalSectionsDirectImageIso f).hom.app F) = b := by
  intro K F Df Dfg HX HY HZ Sf Sg e p b
  let Dg := RingedSpace.moduleDirectImage g.toLRSHom.toShHom
  have he := mixedSections_composition_unit_heq f g K
  have hg₀ := mixedSections_unit_heq g ((Df.mapHomotopyCategory (.up ℤ)).obj K)
  have hA := mixedSections_global_source g ((Df.mapHomotopyCategory (.up ℤ)).obj K)
  have hp := generic_first_layer Df Dg Dfg HY HZ Sg (by rfl) e
    (mixedGlobalSectionsDirectImageIso g) K he hA hg₀
  have hg : p ≫ (mixedGlobalSectionsDirectImageIso g).hom.app
        ((schemeDerivedDirectImage f).obj F) =
      Sg.mapDerivedCategoryFactorsh.inv.app
        ((HY.mapHomotopyCategory (.up ℤ)).obj ((Df.mapHomotopyCategory (.up ℤ)).obj K)) ≫
      (schemeGlobalScalarRestriction g).map
        (HY.rightDerivedFunctorUnit.app ((Df.mapHomotopyCategory (.up ℤ)).obj K)) ≫
      (schemeGlobalScalarRestriction g).map
        ((schemeDerivedGlobalSections Y).map (Df.rightDerivedFunctorUnit.app K)) := by
    apply eq_of_heq
    dsimp only [p, F, HY, HZ, Df, Dfg, Sg, schemeDerivedGlobalSections,
      schemeGlobalScalarRestriction, schemeDerivedDirectImage,
      RingedSpace.derivedModuleDirectImage] at hp ⊢
    simpa only [Category.assoc] using hp
  have hf := mixedSections_unit f K
  exact finish_unit_paste (schemeGlobalScalarRestriction g) p
    ((mixedGlobalSectionsDirectImageIso g).hom.app ((schemeDerivedDirectImage f).obj F))
    (Sg.mapDerivedCategoryFactorsh.inv.app
      ((HY.mapHomotopyCategory (.up ℤ)).obj ((Df.mapHomotopyCategory (.up ℤ)).obj K)))
    (HY.rightDerivedFunctorUnit.app ((Df.mapHomotopyCategory (.up ℤ)).obj K))
    ((schemeDerivedGlobalSections Y).map (Df.rightDerivedFunctorUnit.app K))
    ((mixedGlobalSectionsDirectImageIso f).hom.app F)
    (Sf.mapDerivedCategoryFactorsh.inv.app ((HX.mapHomotopyCategory (.up ℤ)).obj K))
    ((schemeGlobalScalarRestriction f).map (HX.rightDerivedFunctorUnit.app K)) hg hf

end AlgebraicGeometry
