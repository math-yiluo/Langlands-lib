/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison

/-! # Finite exceptional inverse image in fixed coefficient coordinates

Source: Weil blueprint, sk-def-sf-operations (vi), finite-level exceptional inverse image
(blueprint: theorem-f-shriek-finite-coefficients).

The coefficient universe is that of the module values on the actual small sites.
The right adjoint is determined by its ordinary etale compact-support adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- The finite-level transported exceptional inverse image at a specified compactification:
R nu_* followed by the ordinary etale right adjoint, followed by exact nu^*.
It uses the unique-adjoint construction, not an arbitrarily chosen pro-etale adjoint.
The fixed-ring module presentation is canonically equivalent to modules over the constant
coefficient sheaf. No boundedness hypothesis is part of this definition of an ambient
functor; the node's assertion concerns D+ and the bounded constructible scope.
Source: Weil blueprint, sk-def-sf-operations (vi)
(blueprint: theorem-f-shriek-finite-coefficients). -/
def sfFiniteExceptionalAt (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [(Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) c).IsLeftAdjoint] :
    DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :=
  (comparisonLowerStar (ModuleCat.{u + 1} A) Y).rightDerivedFunctor ⋙
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).rightAdjoint ⋙
    (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory

end AlgebraicGeometry.ProEtale
