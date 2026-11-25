/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ExactFunctorDerivedUnit
public import WeilConjectures.CategoryTheory.ExactDegreeZero

/-! # The scalar-unit universal property in the exact-functor interface

Source: Stacks 07A6 and the canonical exact degree-zero interface.
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace SheafExactDegreeZero

attribute [local instance 10000] scalarWeakSheafify

/-- The canonical scalar universal property gives the same unbounded Hom bijections
as the exact-functor predicate. Source: Stacks 07A6; the exact single-functor comparison
(auxiliary; not a blueprint node).
Proof: scalarUniversal_iff expresses the named canonical scalar unit as the map
single(eta) followed by the inverse exact-functor comparison, tested against every
unbounded complex. This is precisely the formula defining Functor.DerivedUnit. Apply
the forward implication of scalarUniversal_iff. No flatness or boundedness is used. -/
theorem scalarUniversal_derivedUnit
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (F : Sheaf J (ModuleCat.{u + 1} R))
    (G : Sheaf J (ModuleCat.{u + 1} S))
    (η : F ⟶ (Sheaf.restrictScalars J φ).obj G)
    (h : scalarUniversal J φ F G η) :
    (Sheaf.restrictScalars J φ).DerivedUnit F G η := by
  exact (scalarUniversal_iff J φ F G η).mp h

end SheafExactDegreeZero
