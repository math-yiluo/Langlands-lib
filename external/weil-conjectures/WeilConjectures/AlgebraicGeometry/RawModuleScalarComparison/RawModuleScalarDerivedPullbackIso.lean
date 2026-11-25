/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RawModuleScalarPullbackComparison
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import all WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientUnshifted

/-! # Derived canonical scalar pullback comparison

## References

* Stacks Project, Tags 03D3 and 03D7, the inverse-image adjunction
-/

@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.RawModuleScalarComparison

/-- Forget scalar operations on a module sheaf. -/
noncomputable abbrev forget (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :=
  moduleAbelianForget Λ X

/-- Scalar forgetting is additive, section by section. -/
instance forget_additive (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    (forget Λ X).Additive := moduleAbelianForget_additive Λ X

/-- Scalar forgetting preserves finite limits, as does its presheaf composite. -/
instance forget_preservesFiniteLimits (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    PreservesFiniteLimits (forget Λ X) := moduleAbelianForget_preservesFiniteLimits Λ X

/-- Scalar forgetting preserves finite colimits by the constant-coefficient theorem. -/
instance forget_preservesFiniteColimits (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u}) :
    PreservesFiniteColimits (forget Λ X) := moduleAbelianForget_preservesFiniteColimits Λ X

/-- The scalar pullback comparison has the forgotten module unit as its adjoint. -/
theorem pullback_unit (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
        ((forget Λ Y).obj F) ≫
      (lowerStar AddCommGrpCat.{u + 1} f).map (pullback Λ f F) =
      (forget Λ Y).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F) := by
  change (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
    ((moduleAbelianUpperStarComparison Λ f).app F) = _
  exact Equiv.apply_symm_apply _ _

end AlgebraicGeometry.Etale.RawModuleScalarComparison
