/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedQcqsPushforwardContinuitySupplement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.AlgebraicGeometry.CondensedUnderivedPushforwardContinuity

/-! # The degree-zero consequence of qcqs pushforward continuity -/

@[expose] public section

universe u
open CategoryTheory Limits Abelian
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Functor

/-- Degree zero of the derived functor on single complexes is the original left exact
functor, naturally in the module.
Source: the injective-resolution computation of the zeroth right derived functor.
(blueprint: lem-weil-pbc-condensed-underived-pushforward-continuity) -/
noncomputable def singleComplexRightDerivedZeroIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] [HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] :
    HomologicalComplex.single C (.up ℤ) 0 ⋙ DerivedCategory.Q ⋙
      F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor D 0 ≅ F :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (DerivedCategory.singleFunctorIsoCompQ C 0).symm
      (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor D 0) ≪≫
    Functor.isoWhiskerRight (DerivedCategory.Plus.singleFunctorιIso C 0).symm
      (F.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor D 0) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C 0)
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight F.rightDerivedFunctorPlusCompatibility.symm
          (DerivedCategory.homologyFunctor D 0) ≪≫
        Functor.associator _ _ _) ≪≫
    F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0 ≪≫
    F.rightDerivedZeroIsoSelf

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

end AlgebraicGeometry.ProEtale.CondensedRing
