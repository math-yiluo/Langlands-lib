/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleExceptionalObjectComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison

/-!
# Exceptional adjunction transport from etale to pro-etale sheaves

Source: blueprint main-20261015, chap-Construction-of-f,
theorem-f-shriek-finite-coefficients, final restriction paragraph; the explicit transport
argument of the DAG (blueprint: lem-sf-etale-proetale-exceptional-transport).

The domain below uses intrinsic constructible cohomology, rather than assuming etale
origin. All Tor predicates test every module sheaf on the respective site.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The intrinsic pro-etale domain of transport: bounded cohomology, every cohomology
sheaf constructible on a global finite partition, and finite Tor amplitude against all
pro-etale module sheaves. Source: blueprint main-20261015,
theorem-f-shriek-finite-coefficients, final restriction paragraph
(blueprint: lem-sf-etale-proetale-exceptional-transport). -/
def exceptionalTransportProEtaleObjects (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) : ObjectProperty
      (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :=
  fun K ↦ _root_.DerivedCategory.TStructure.t.bounded K ∧
    (∀ i : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf T A
      ((_root_.DerivedCategory.homologyFunctor _ i).obj K)) ∧
    ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) T a b K

end AlgebraicGeometry.ProEtale
