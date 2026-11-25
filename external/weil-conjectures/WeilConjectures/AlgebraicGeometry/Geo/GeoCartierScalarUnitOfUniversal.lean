/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClassDefsSupplement
public import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement
import WeilConjectures.AlgebraicGeometry.ScalarUniversalDerivedUnit
import WeilConjectures.AlgebraicGeometry.ExactFunctorDerivedUnit
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement

/-! # Canonical scalar universality gives the Cartier scalar-unit predicate -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify

private theorem derivedUnit_assoc
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (U : A ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (F : B) (G : A) (η : F ⟶ U.obj G) (h : U.DerivedUnit F G η) :
    ∀ K : DerivedCategory A,
      Function.Bijective (fun f : (DerivedCategory.singleFunctor A 0).obj G ⟶ K ↦
        ((DerivedCategory.singleFunctor B 0).map η ≫
          (U.mapDerivedCategorySingleFunctor 0).inv.app G) ≫ U.mapDerivedCategory.map f) := by
  intro K
  simpa only [Category.assoc] using h K

/-- The canonical scalar universal property implies the Cartier scalar-unit predicate.
Source: blueprint lemma-cycle-class-cartier-divisor, coefficient paragraph, and the canonical
exact-degree-zero scalar interface (blueprint: lem-sfb-geo-cartier-scalar-unit-of-universal).
Proof: The existing scalarUniversal_derivedUnit theorem expresses the canonical scalar
universal property in the abstract exact-functor interface. A general category lemma
reassociates its composition with single(eta) and the inverse exact-single comparison.
Unfold GeoCartierScalarUnit and IsDerivedBaseChange to obtain precisely that formula.
All unbounded test complexes remain. No finiteness or flatness assumption is used. -/
theorem geoCartierScalarUnit_of_scalarUniversal
    {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (φ : R →+* S) (Z : Scheme.{u})
    (F : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} R))
    (G : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} S))
    (η : F ⟶ (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).obj G)
    (h : SheafExactDegreeZero.scalarUniversal (Scheme.ProEt.topology Z) φ F G η) :
    GeoCartierScalarUnit φ Z F G η := by
  have hh := SheafExactDegreeZero.scalarUniversal_derivedUnit _ φ F G η h
  unfold GeoCartierScalarUnit Sheaf.IsDerivedBaseChange
  exact derivedUnit_assoc _ F G η hh

end AlgebraicGeometry.ProEtale
