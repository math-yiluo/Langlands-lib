/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows

/-! # Constant-object pullback comparisons

Source: blueprint vector integration, compatibility with restriction.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

attribute [local irreducible] _root_.DerivedCategory.singleFunctors
  Functor.leftDerivedFunctor upperStar

/-- The concrete constant-object pullback has its specified two factors.
Source: the definition of ordinaryFiniteUnitPullback, blueprint vector integration.
(auxiliary; not a blueprint node). -/
theorem ordinaryFiniteUnitPullback_hom (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ordinaryFiniteUnitPullback A f).hom =
      (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) f).hom.app
        (ordinaryFiniteConstant A Y) ≫
      (_root_.DerivedCategory.singleFunctor _ 0).map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).hom.app
          (ModuleCat.of A A)) := rfl

end AlgebraicGeometry.Etale
