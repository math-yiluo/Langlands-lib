/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility
public import WeilConjectures.AlgebraicGeometry.RawRestrictedDerivedComparison

/-! # Fixed-coefficient raw evaluation on an etale chart

Source: Stacks Project, Tags 03Q8, 072W and 0GIT.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar

/-- Evaluate a raw class and identify its coefficient with pullback from the fixed base.
Every factor is the canonical evaluation or inverse-image composition comparison.
Source: Stacks Project, Tags 03Q8 and 0GIT.
(blueprint: def-sc-raw-fixed-derived-comparison). -/
noncomputable def rawFixedDerivedComparison {B T Y : Scheme.{u}}
    (h : Y ⟶ B) (g : Y ⟶ T)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (q : ℤ) (U : B.Etale) :
    AddCommGrpCat.of ((DerivedCategory.Plus.singleFunctor _ 0).obj
      (((h)^*[AddCommGrpCat.{u + 1}]).obj ((abelianComparisonFree B).obj U)) ⟶
      ((D+((g)^*[AddCommGrpCat.{u + 1}])).obj K)⟦q⟧) ⟶
    (cohomology AddCommGrpCat.{u + 1} (pullback U.hom h) q).obj
      (((pullback.snd U.hom h ≫ g)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategory.obj
        K.obj) :=
  rawRestrictedDerivedComparison h q ((D+((g)^*[AddCommGrpCat.{u + 1}])).obj K) U ≫
    (cohomology AddCommGrpCat.{u + 1} (pullback U.hom h) q).map
      ((Functor.mapDerivedCategoryNatIso
          (upperStarComp AddCommGrpCat.{u + 1} (pullback.snd U.hom h) g) ≪≫
        (Functor.mapDerivedCategoryCompIso
          (upperStar AddCommGrpCat.{u + 1} g)
          (upperStar AddCommGrpCat.{u + 1} (pullback.snd U.hom h))).symm).inv.app K.obj)


end AlgebraicGeometry.Etale
