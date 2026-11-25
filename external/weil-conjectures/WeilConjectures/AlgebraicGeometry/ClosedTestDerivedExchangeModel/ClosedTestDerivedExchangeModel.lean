/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClosedTestDerivedExchangeModel.ClosedTestDerivedExchangeMaps

import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Restriction

import WeilConjectures.AlgebraicGeometry.ClosedTestSectionSteps.ClosedTestSectionLocalization
import WeilConjectures.AlgebraicGeometry.ClosedTestSectionSteps.ClosedTestClosedEvaluation
import WeilConjectures.AlgebraicGeometry.NonaffineClosedTestExchangeIdentification.NonaffineClosedTestExchangeIdentification

/-!
# The canonical derived exchange on closed lifted tests

Source: Stacks Project, Tags 09BL and 0D6F, and the unit--counit calculation
(blueprint: lem-sfb-closed-test-derived-exchange-model).

## Main definitions

* `exchange`: the specified derived adjunction mate.
* `testRestriction`: restriction along the actual closed test-fibre map.
* `restrictPush`: the coefficient comparison induced by the ordinary section identity.

## Main statements

* `closed_test_derived_exchange_model`: the two normalized derived isomorphisms.
* `closed_test_test_naturality`: compatibility with admissible test maps.
* `section_comparison_base_change_naturality`: compatibility with localization cubes.
* `derived_restriction_localization`: localization of canonical restriction.
* `closed_test_coefficient_naturality`: compatibility with actual coefficient maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ClosedTestDerivedExchangeModel

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [IsCommMonObj Λ] in
private theorem pushSectionsIso_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.whiskerRight (CondensedRing.lowerStarComp Λ f g).hom
        (condensedModuleSections Λ Z) ≫ (pushSectionsIso Λ (f ≫ g)).hom =
      Functor.whiskerLeft (CondensedRing.lowerStar Λ f) (pushSectionsIso Λ g).hom ≫
        (pushSectionsIso Λ f).hom := by
  apply NatTrans.ext
  funext M
  let σZ := Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology Z) Ab.{u + 1}
    (Scheme.ProEt.isTerminalMkId Z)
  let σY := Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology Y) Ab.{u + 1}
    (Scheme.ProEt.isTerminalMkId Y)
  let σX := Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X) Ab.{u + 1}
    (Scheme.ProEt.isTerminalMkId X)
  change ((sheafSections (Scheme.ProEt.topology Z) Ab.{u + 1}).obj
      (op (Scheme.ProEt.mk (𝟙 Z)))).map
        ((CondensedRing.lowerStarComp Λ f g).hom.app M).hom ≫
      (σZ.inv.app ((CondensedRing.lowerStar Λ (f ≫ g)).obj M).X ≫
        (ProEtale.globalSectionsLowerStarIso Ab.{u + 1} (f ≫ g)).hom.app M.X ≫
          σX.hom.app M.X) =
    (σZ.inv.app ((CondensedRing.lowerStar Λ g).obj
        ((CondensedRing.lowerStar Λ f).obj M)).X ≫
      (ProEtale.globalSectionsLowerStarIso Ab.{u + 1} g).hom.app
        ((CondensedRing.lowerStar Λ f).obj M).X ≫
      σY.hom.app ((CondensedRing.lowerStar Λ f).obj M).X) ≫
        (σY.inv.app ((CondensedRing.lowerStar Λ f).obj M).X ≫
          (ProEtale.globalSectionsLowerStarIso Ab.{u + 1} f).hom.app M.X ≫
            σX.hom.app M.X)
  rw [reassoc_of% σZ.inv.naturality]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [CondensedRing.lowerStarComp_hom_app_hom,
    reassoc_of% ProEtale.globalSectionsLowerStarIso_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem derivedPushComp_eq_conjugate {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.rightDerivedFunctorCompIso' (CondensedRing.lowerStar Λ f)
        (CondensedRing.lowerStar Λ g) (CondensedRing.lowerStarComp Λ f g) =
      conjugateIsoEquiv ((adj Λ g).comp (adj Λ f)) (adj Λ (f ≫ g))
        (pullComp Λ f g) := by
  apply Iso.ext
  apply Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
    (CondensedRing.upperStarLowerStarAdjunction Λ f)
    (CondensedRing.upperStarLowerStarAdjunction Λ g)
    (CondensedRing.upperStarLowerStarAdjunction Λ (f ≫ g))
  exact congrArg Iso.hom (CondensedRing.conjugateIsoEquiv_upperStarComp Λ f g).symm

set_option backward.isDefEq.respectTransparency false in
private theorem derived_unit_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    (adj Λ (f ≫ g)).unit.app M ≫
        (CondensedRing.moduleObjectDerivedPushforward Λ (f ≫ g)).map
          ((pullComp Λ f g).hom.app M) =
      (adj Λ g).unit.app M ≫
        (CondensedRing.moduleObjectDerivedPushforward Λ g).map
          ((adj Λ f).unit.app ((pull Λ g).obj M)) ≫
        (Functor.rightDerivedFunctorCompIso' (CondensedRing.lowerStar Λ f)
          (CondensedRing.lowerStar Λ g) (CondensedRing.lowerStarComp Λ f g)).hom.app
            ((pull Λ f).obj ((pull Λ g).obj M)) := by
  have hu := unit_conjugateEquiv ((adj Λ g).comp (adj Λ f)) (adj Λ (f ≫ g))
    (pullComp Λ f g).hom M
  rw [← conjugateIsoEquiv_apply_hom, ← derivedPushComp_eq_conjugate,
    Adjunction.comp_unit_app] at hu
  rw [← hu, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem pushDerivedSectionsIso_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.whiskerRight
        (Functor.rightDerivedFunctorCompIso' (CondensedRing.lowerStar Λ f)
          (CondensedRing.lowerStar Λ g) (CondensedRing.lowerStarComp Λ f g)).hom
        (condensedModuleSections Λ Z).rightDerivedFunctor ≫
        (pushDerivedSectionsIso Λ (f ≫ g)).hom =
      Functor.whiskerLeft (CondensedRing.moduleObjectDerivedPushforward Λ f)
          (pushDerivedSectionsIso Λ g).hom ≫ (pushDerivedSectionsIso Λ f).hom := by
  exact Functor.rightDerivedFunctorCompIso'_assoc
    (CondensedRing.lowerStar Λ f) (CondensedRing.lowerStar Λ g)
    (condensedModuleSections Λ Z) (CondensedRing.lowerStar Λ (f ≫ g))
    (condensedModuleSections Λ Y) (condensedModuleSections Λ X)
    (CondensedRing.lowerStarComp Λ f g) (pushSectionsIso Λ g)
    (pushSectionsIso Λ (f ≫ g)) (pushSectionsIso Λ f) (pushSectionsIso_comp Λ f g)

set_option backward.isDefEq.respectTransparency false in
private theorem restriction_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    (restriction Λ (f ≫ g)).app M ≫
        (condensedModuleSections Λ X).rightDerivedFunctor.map
          ((pullComp Λ f g).hom.app M) =
      (restriction Λ g).app M ≫ (restriction Λ f).app ((pull Λ g).obj M) := by
  let GZ := (condensedModuleSections Λ Z).rightDerivedFunctor
  let GY := (condensedModuleSections Λ Y).rightDerivedFunctor
  let GX := (condensedModuleSections Λ X).rightDerivedFunctor
  let Rf := CondensedRing.moduleObjectDerivedPushforward Λ f
  let Rg := CondensedRing.moduleObjectDerivedPushforward Λ g
  let Rfg := CondensedRing.moduleObjectDerivedPushforward Λ (f ≫ g)
  let P := (pull Λ f).obj ((pull Λ g).obj M)
  let d := Functor.rightDerivedFunctorCompIso' (CondensedRing.lowerStar Λ f)
    (CondensedRing.lowerStar Λ g) (CondensedRing.lowerStarComp Λ f g)
  have hη := congrArg GZ.map (derived_unit_comp Λ f g M)
  have hd := NatTrans.congr_app (pushDerivedSectionsIso_comp Λ f g) P
  have hn := (pushDerivedSectionsIso Λ g).hom.naturality
    ((adj Λ f).unit.app ((pull Λ g).obj M))
  have hn' := (pushDerivedSectionsIso Λ (f ≫ g)).hom.naturality
    ((pullComp Λ f g).hom.app M)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hd hn hn'
  dsimp only [restriction, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  change (GZ.map ((adj Λ (f ≫ g)).unit.app M) ≫
      (pushDerivedSectionsIso Λ (f ≫ g)).hom.app ((pull Λ (f ≫ g)).obj M)) ≫
        GX.map ((pullComp Λ f g).hom.app M) =
    (GZ.map ((adj Λ g).unit.app M) ≫
      (pushDerivedSectionsIso Λ g).hom.app ((pull Λ g).obj M)) ≫
        GY.map ((adj Λ f).unit.app ((pull Λ g).obj M)) ≫
          (pushDerivedSectionsIso Λ f).hom.app P
  simp only [Category.assoc]
  rw [← hn']
  rw [← GZ.map_comp_assoc, hη]
  simp only [Functor.map_comp, Category.assoc] at hd ⊢
  change GZ.map ((adj Λ g).unit.app M) ≫
      GZ.map (Rg.map ((adj Λ f).unit.app ((pull Λ g).obj M))) ≫
        GZ.map (d.hom.app P) ≫ (pushDerivedSectionsIso Λ (f ≫ g)).hom.app P = _
  rw [hd]
  rw [← reassoc_of% hn]

section Coefficients

variable {Λ} {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ'] [IsCommMonObj Λ'] (c : Λ ⟶ Λ') [IsMonHom c]

/-- The existing exact restriction of scalars on ordinary unbounded derived categories.
Source: scalar clause and Tag 0D6E
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def restrict (X : Scheme.{u}) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ' X)) ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :=
  (Mod.comap (coefficientMap c X)).mapDerivedCategory

/-- The canonical right-derived direct-image coefficient comparison. Its direction is fixed
by the ordinary section identity; no preservation of injectives by restriction is assumed.
Source: the statement's coefficient clause and proof step 10
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def restrictPush {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.moduleObjectDerivedPushforward Λ' f ⋙ restrict c Y ⟶
      restrict c X ⋙ CondensedRing.moduleObjectDerivedPushforward Λ f :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
      (CondensedRing.lowerStar Λ' f) (Mod.comap (coefficientMap c Y))).inv ≫
    Functor.rightDerivedPullback (Mod.comap (coefficientMap c X))
      (CondensedRing.comapLowerStarIso c f).hom

/-- The derived coefficient map on global sections, induced by the literal underlying
section identity and the universal right-derived unit.
Source: coefficient clause, proof step 10
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def restrictSections (X : Scheme.{u}) :
    (condensedModuleSections Λ' X).rightDerivedFunctor ⟶
      restrict c X ⋙ (condensedModuleSections Λ X).rightDerivedFunctor :=
  Functor.rightDerivedPullback (Mod.comap (coefficientMap c X)) (𝟙 _)

/-- Coefficient restriction on localized sections uses the existing exact pullback comparison.
Source: coefficient clause and Tag 0D6F
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def restrictSectionsOver {X W : Scheme.{u}} (b : W ⟶ X) :
    sectionsOver Λ' b ⟶ restrict c X ⋙ sectionsOver Λ b :=
  Functor.whiskerLeft (pull Λ' b) (restrictSections c W) ≫
    Functor.whiskerRight (CondensedRing.derivedComapUpperStarIso c b).hom
      (condensedModuleSections Λ W).rightDerivedFunctor

/-- The actual ordinary extension unit in degree zero, with exact restriction of scalars.
Source: the final sentence of the item, x ↦ 1 tensor x
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def scalarUnit (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (DerivedCategory.singleFunctor _ 0).obj M ⟶
      (restrict c X).obj ((DerivedCategory.singleFunctor _ 0).obj
        ((Mod.extendScalars (coefficientMap c X)).obj M)) :=
  (DerivedCategory.singleFunctor _ 0).map
      ((Mod.extendRestrictAdjunction (coefficientMap c X)).unit.app M) ≫
    ((Mod.comap (coefficientMap c X)).mapDerivedCategorySingleFunctor 0).inv.app
      ((Mod.extendScalars (coefficientMap c X)).obj M)

/-- Commutativity of the section-comparison square for the actual coefficient map.
Source: coefficient clause, proof steps 10--11
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def CoefficientSectionComparison {X U T W : Scheme.{u}} {f : X ⟶ U} {b : W ⟶ U}
    {h : T ⟶ X} {fW : T ⟶ W} (w : CommSq h fW f b)
    (N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))) : Prop :=
  (restrictSectionsOver c b).app
        ((CondensedRing.moduleObjectDerivedPushforward Λ' f).obj N) ≫
      (sectionsOver Λ b).map ((restrictPush c f).app N) ≫
      (sectionComparison Λ w).app ((restrict c X).obj N) =
    (sectionComparison Λ' w).app N ≫ (restrictSectionsOver c h).app N

/-- Commutativity of derived restriction and the actual coefficient section map.
Source: coefficient clause and Tag 0D6F
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def CoefficientRestriction {X W W' : Scheme.{u}} (b : W ⟶ X) (a : W' ⟶ W)
    (N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))) : Prop :=
  (restrictionOver Λ' b a).app N ≫ (restrictSectionsOver c (a ≫ b)).app N =
    (restrictSectionsOver c b).app N ≫
      (restrictionOver Λ b a).app ((restrict c X).obj N)

end Coefficients

end AlgebraicGeometry.ProEtale.ClosedTestDerivedExchangeModel
