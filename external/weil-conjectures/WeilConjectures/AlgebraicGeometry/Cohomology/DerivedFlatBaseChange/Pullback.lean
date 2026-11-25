/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategoryComparison
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatBaseChangeSheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory

/-!
# Derived pullback along a flat morphism

For a flat morphism `h : T' ⟶ T`, pullback of `𝒪_T`-modules is exact, so the derived pullback
of a module placed in degree `0` is its ordinary pullback.
-/

@[expose] public section

universe w u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The equivalence `schemeDerivedCategoryEquiv X` sends a module placed in degree `0` to the same
module placed in degree `0`. -/
noncomputable def schemeDerivedCategoryEquivFunctorSingleIso {X : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] (M : X.Modules) :
    (schemeDerivedCategoryEquiv.{w} X).functor.obj ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj M :=
  (schemeDerivedCategoryEquiv.{w} X).functor.mapIso
      ((DerivedCategory.singleFunctorIsoCompQ
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).app M) ≪≫
    (qCompSchemeDerivedCategoryEquivFunctor.{w} X).app _ ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app M).symm

/-- For flat `h`, the derived pullback of a module `M` placed in degree `0` is `h^* M` placed in
degree `0`. -/
noncomputable def derivedPullbackSingleFunctorIsoOfFlat
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {T T' : Scheme.{u}} (h : T' ⟶ T) [Flat h] (M : T.Modules) :
    (derivedPullback h).obj ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((Scheme.Modules.pullback h).obj M) :=
  (eqToIso (derivedPullback_def h)).app _ ≪≫
    (schemeDerivedCategoryEquiv T').inverse.mapIso
      ((Scheme.Modules.derivedPullback h).mapIso (schemeDerivedCategoryEquivFunctorSingleIso M) ≪≫
        (Scheme.Modules.pullback h).singleFunctorCompLeftDerivedFunctorIso.app M ≪≫
        (schemeDerivedCategoryEquivFunctorSingleIso _).symm) ≪≫
    (schemeDerivedCategoryEquiv T').unitIso.symm.app _

end AlgebraicGeometry
