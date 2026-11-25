/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Upper.UpperStarSingleTensorDefinitions

/-!
# The scalar coefficient comparison as a single-sheaf comparison

## References

* Stacks 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory upperStar lowerStar

/-- The scalar coefficient comparison is the single-sheaf comparison for its
ordinary coefficient iso. -/
theorem scalarCoefficientSinglePullbackIso_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {Z W : Scheme.{u}} (f : Z ⟶ W) :
    upperStarSingleCoefficientIso A f (scalarCoefficientSheafPullbackIso φ f) =
      scalarCoefficientPullbackIso φ f := by
  rfl

end AlgebraicGeometry.Etale
