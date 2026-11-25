/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import Mathlib.CategoryTheory.Filtered.Basic

/-! # Data for applying derived continuity to a section comparison

Source: Stacks Project, Tags 03Q9 and 0GIT.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- A source colimit and a projection-pullback presentation of its comparison map.
The target is not assumed to be a colimit, and the comparison is not assumed invertible.
Source: Stacks Project, Tags 03Q9 and 0GIT
(blueprint: def-weil-pbc-global-cohomology-continuity-presentation). -/
structure GlobalCohomologyContinuityPresentation
    (T : Scheme.{v})
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) {A B : AddCommGrpCat.{v + 1}} (m : A ⟶ B) where
  I : Type v
  [category : SmallCategory I]
  [cofiltered : IsCofiltered I]
  D : I ⥤ Scheme.{v}
  c : Cone D
  isLimit : IsLimit c
  [compact : ∀ i, CompactSpace (D.obj i)]
  [quasiSeparated : ∀ i, QuasiSeparatedSpace (D.obj i)]
  [affine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  t : D ⟶ (Functor.const I).obj T
  p : c.pt ⟶ T
  over : ∀ i, c.π.app i ≫ t.app i = p
  F : Iᵒᵖ ⥤ AddCommGrpCat.{v + 1}
  e : ∀ i : I, F.obj (op i) ≅
    (cohomology AddCommGrpCat.{v + 1} (D.obj i) n).obj
      ((upperStar AddCommGrpCat.{v + 1} (t.app i)).mapDerivedCategory.obj K.obj)
  transition : ∀ {i j : I} (f : i ⟶ j), F.map f.op =
      (e j).hom ≫
      (Etale.cohomology AddCommGrpCat.{v + 1} (D.obj j) n).map
        ((Etale.mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
          (D.map f)).unit.app
            ((Etale.upperStar AddCommGrpCat.{v + 1} (t.app j)).mapDerivedCategory.obj
              K.obj)) ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
        ((Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          AddCommGrpCat.{v + 1} (D.map f)).hom.app
            ((Etale.upperStar AddCommGrpCat.{v + 1} (D.map f)).mapDerivedCategory.obj
              ((Etale.upperStar AddCommGrpCat.{v + 1} (t.app j)).mapDerivedCategory.obj
                K.obj))) ≫
      (Etale.cohomology AddCommGrpCat.{v + 1} (D.obj i) n).map
        ((Functor.mapDerivedCategoryNatIso
          (Etale.upperStarComp AddCommGrpCat.{v + 1} (D.map f) (t.app j)
            (t.app i) ((Category.comp_id (t.app i)).symm.trans (t.naturality f).symm)) ≪≫
          (Functor.mapDerivedCategoryCompIso
            (Etale.upperStar AddCommGrpCat.{v + 1} (t.app j))
            (Etale.upperStar AddCommGrpCat.{v + 1} (D.map f))).symm).inv.app K.obj) ≫
      (e i).inv
  sourceLegs : F ⟶ (Functor.const Iᵒᵖ).obj A
  sourceIsColimit : IsColimit (Cocone.mk A sourceLegs)
  limitIso : B ≅ (cohomology AddCommGrpCat.{v + 1} c.pt n).obj
    ((upperStar AddCommGrpCat.{v + 1} p).mapDerivedCategory.obj K.obj)
  restriction : ∀ i : I, (sourceLegs.app (op i)) ≫ m =
      (e i).hom ≫
      (Etale.cohomology AddCommGrpCat.{v + 1} (D.obj i) n).map
        ((Etale.mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
          (c.π.app i)).unit.app
            ((Etale.upperStar AddCommGrpCat.{v + 1} (t.app i)).mapDerivedCategory.obj
              K.obj)) ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
        ((Etale.rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
          AddCommGrpCat.{v + 1} (c.π.app i)).hom.app
            ((Etale.upperStar AddCommGrpCat.{v + 1} (c.π.app i)).mapDerivedCategory.obj
              ((Etale.upperStar AddCommGrpCat.{v + 1} (t.app i)).mapDerivedCategory.obj
                K.obj))) ≫
      (Etale.cohomology AddCommGrpCat.{v + 1} c.pt n).map
        ((Functor.mapDerivedCategoryNatIso
          (Etale.upperStarComp AddCommGrpCat.{v + 1} (c.π.app i) (t.app i) p
            (over i).symm) ≪≫
          (Functor.mapDerivedCategoryCompIso
            (Etale.upperStar AddCommGrpCat.{v + 1} (t.app i))
            (Etale.upperStar AddCommGrpCat.{v + 1} (c.π.app i))).symm).inv.app K.obj) ≫
      limitIso.inv

end AlgebraicGeometry.Etale
