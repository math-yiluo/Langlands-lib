/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Etale.EtaleDegreeZeroHom

/-! # The two factors of the degree-zero restriction comparison

Source: blueprint vector integration, compatibility with restriction.
(blueprint: lem-amb-etale-single-restriction-factors).
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

/-- The specified degree-zero restriction comparison is its actual two-factor
construction, without unfolding the derived functors themselves.
Source: blueprint vector integration, restriction of the degree-zero correspondence.
(blueprint: lem-amb-etale-single-restriction-factors). -/
theorem etaleSingleRestrictionIso_eq (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] :
    etaleSingleRestrictionIso A f =
      singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) f ≪≫
        Functor.isoWhiskerRight
          (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) f inferInstance)
          (_root_.DerivedCategory.singleFunctor _ 0) := by
  unfold etaleSingleRestrictionIso
  rfl

end AlgebraicGeometry.Etale
