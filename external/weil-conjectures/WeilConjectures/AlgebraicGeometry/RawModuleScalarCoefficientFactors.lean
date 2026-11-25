/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageRawOverCoefficient
public import
  WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomPresheaf

/-! # Coefficient factors of the derived scalar pullback square

Source: Stacks Project, Tags 03D7 and 03Q8.
(blueprint: def-sbc-raw-scalar-coefficient-factors).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The last two module pullback factors.
Source: Stacks Project, Tag 03Q8.
(blueprint: def-sbc-raw-scalar-coefficient-factors). -/
noncomputable def moduleCoefficientFactor
    (Λ : Type (u + 1)) [CommRing Λ] {W : Scheme.{u}}
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (A B : Over W) (f : A ⟶ B) :
    (upperStar (ModuleCat.{u + 1} Λ) f.left).mapDerivedCategoryPlus.obj
        (((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} Λ) B.hom).obj G))⟦q⟧) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar (ModuleCat.{u + 1} Λ) A.hom).obj G))⟦q⟧ :=
  ((moduleUpperStar Λ f.left).mapDerivedCategoryPlus.commShiftIso q).hom.app
    (higherDirectImageRawOverComplex Λ G B) ≫
    (shiftFunctor _ q).map (higherDirectImageRawOverCoefficient Λ G f)

/-- The last two abelian pullback factors.
Source: Stacks Project, Tag 03Q8.
(blueprint: def-sbc-raw-scalar-coefficient-factors). -/
noncomputable def abelianCoefficientFactor
    {W : Scheme.{u}} (G : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
    (A B : Over W) (f : A ⟶ B) :
    (upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.obj
        (((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar AddCommGrpCat.{u + 1} B.hom).obj G))⟦q⟧) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} A.hom).obj G))⟦q⟧ :=
  ((upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlus.commShiftIso q).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} B.hom).obj G)) ≫
    (shiftFunctor _ q).map
      (((upperStar AddCommGrpCat.{u + 1} f.left).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          ((upperStarComp AddCommGrpCat.{u + 1} f.left B.hom A.hom
            (Over.w f).symm).inv.app G))

end AlgebraicGeometry.Etale
