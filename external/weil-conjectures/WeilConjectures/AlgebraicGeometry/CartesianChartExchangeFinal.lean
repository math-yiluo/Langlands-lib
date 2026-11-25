/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CartesianChartClassPullback

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

lemma chartClassPullback_postcomp {B T T' : Scheme.{u}}
    (a : T ⟶ B) (b : T' ⟶ T) (a' : T' ⟶ B) (ha : a' = b ≫ a)
    (V : B.Etale) (U : T'.Etale) (r : U.left ⟶ V.left)
    (hr : IsPullback r U.hom V.hom a')
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (q : ℤ)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((a)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree B).obj V)) ⟶ K⟦q⟧)
    (L : DerivedCategory.Plus (Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (e : ((D+((b)^*[AddCommGrpCat.{u + 1}])).obj K)⟦q⟧ ⟶ L)
    (s : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((a')^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree B).obj V)) ⟶ L)
    (h : (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp AddCommGrpCat.{u + 1} b a a' ha).hom.app
          ((abelianComparisonFree B).obj V)) ≫
        (((b)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ ≫
        (D+((b)^*[AddCommGrpCat.{u + 1}])).map z ≫
        (D+((b)^*[AddCommGrpCat.{u + 1}]).commShiftIso q).hom.app K ≫ e = s) :
    cartesianChartClassPullback a b a' ha V U r hr K q z ≫ e =
      (DerivedCategory.Plus.singleFunctor _ 0).map
        (abelianFreeRepresentablePullbackSquareIso a' V U r hr).hom ≫ s := by
  dsimp only [cartesianChartClassPullback]
  simpa only [Category.assoc] using congrArg
    ((DerivedCategory.Plus.singleFunctor _ 0).map
      (abelianFreeRepresentablePullbackSquareIso a' V U r hr).hom ≫ ·) h

end AlgebraicGeometry.Etale
