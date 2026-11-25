/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTrianglePullback
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianCoefficientComparison


public import WeilConjectures.AlgebraicGeometry.RawModuleScalarPullbackComparison
public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawTrianglePullbackExtension

/-! # Degree-zero source factors

Source: Stacks Project, Tags 03D7 and 03Q8, and derived single comparisons.
(blueprint: def-sbc-raw-scalar-source-factors).
-/

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
/-- The source part of the scalar comparison, as a fixed derived morphism.
Source: Stacks Project, Tags 03D7 and 03Q8.
(blueprint: def-sbc-raw-scalar-source-factors). -/
noncomputable def scalarSourceFactor
    (Λ : Type (u + 1)) [CommRing Λ] {S Y : Scheme.{u}} (h : Y ⟶ S)
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (E : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (t : E ⟶ (moduleAbelianForget Λ S).obj L) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} h).obj E) ⟶
      (moduleAbelianForget Λ Y).mapDerivedCategoryPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} Λ) h).obj L)) :=
  (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStar AddCommGrpCat.{u + 1} h).map t ≫
        RawModuleScalarComparison.pullback Λ h L) ≫
    ((moduleAbelianForget Λ Y).mapDerivedCategoryPlusSingleFunctor 0).inv.app
      ((upperStar (ModuleCat.{u + 1} Λ) h).obj L)

/-- The first two module pullback factors.
Source: Stacks Project, Tag 03Q8.
(blueprint: def-sbc-raw-scalar-source-factors). -/
noncomputable def moduleSourceFactor
    (Λ : Type (u + 1)) [CommRing Λ] {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar (ModuleCat.{u + 1} Λ) h').obj L) ⟶
      (upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategoryPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} Λ) h).obj L)) :=
  rawTriangleSource (upperStar (ModuleCat.{u + 1} Λ) h) (upperStar (ModuleCat.{u + 1} Λ) h')
    (upperStar (ModuleCat.{u + 1} Λ) a)
    (DerivedCategory.Plus.singleFunctor _ 0) (DerivedCategory.Plus.singleFunctor _ 0)
    (upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategoryPlus
    (upperStarComp (ModuleCat.{u + 1} Λ) a h h' w.symm).hom
    ((upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategoryPlusSingleFunctor 0).inv L

/-- The first two abelian pullback factors.
Source: Stacks Project, Tag 03Q8.
(blueprint: def-sbc-raw-scalar-source-factors). -/
noncomputable def abelianSourceFactor
    {S Y Y' : Scheme.{u}} (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (E : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} h').obj E) ⟶
      (upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar AddCommGrpCat.{u + 1} h).obj E)) :=
  (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp AddCommGrpCat.{u + 1} a h h' w.symm).hom.app E) ≫
    ((upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlusSingleFunctor 0).inv.app
      ((upperStar AddCommGrpCat.{u + 1} h).obj E)

end AlgebraicGeometry.Etale
