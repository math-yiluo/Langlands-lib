/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # The unshifted target of an exact realization composite -/

/- Repair note: this explicit constructor is delivered together with its DAG node. -/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- Compose the exact-single comparison for the first realization, a supplied
scalar endpoint, the exact-single comparison for the finite realization, its
ordinary line map and the final exact-single comparison.

Source: coefficient changes (1), exact realization of one finite reduction.
(blueprint: def-exact-realization-target-zero).
This is an explicit construction; it uses no existence theorem or chosen endpoint. -/
@[irreducible] def exactRealizationTargetZero
    {A B C D E : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D] [HasDerivedCategory E]
    (F : A ⥤ B) (T : DerivedCategory B ⥤ DerivedCategory C) (G : C ⥤ D) (H : D ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    {P : A} {L : B} {N : C} {Q : D} (i : F.obj P ⟶ L)
    (j : T.obj ((DerivedCategory.singleFunctor B 0).obj L) ⟶
      (DerivedCategory.singleFunctor C 0).obj N) (q : G.obj N ⟶ Q) :
    H.mapDerivedCategory.obj (G.mapDerivedCategory.obj
        (T.obj (F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor A 0).obj P)))) ⟶
      (DerivedCategory.singleFunctor E 0).obj (H.obj Q) :=
  H.mapDerivedCategory.map (G.mapDerivedCategory.map (T.map
      ((F.mapDerivedCategorySingleFunctor 0).hom.app P ≫
        (DerivedCategory.singleFunctor B 0).map i))) ≫
    H.mapDerivedCategory.map
      (G.mapDerivedCategory.map j ≫ (G.mapDerivedCategorySingleFunctor 0).hom.app N ≫
        (DerivedCategory.singleFunctor D 0).map q) ≫
    (H.mapDerivedCategorySingleFunctor 0).hom.app Q

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
