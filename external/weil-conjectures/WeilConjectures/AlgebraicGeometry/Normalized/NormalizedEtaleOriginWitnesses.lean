/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ringed.RingedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
public import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedOriginScalarComparisons
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonFiniteLevel
import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedOriginComparisonCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison

/-!
# Compatible etale origins of normalized finite-coefficient towers

The fixed-ring presentation is used through its canonical coefficient
realization. Index n denotes the positive exponent n+1. No level is omitted.

## References

* Stacks Project, Tag 09B1
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

variable (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
  (d : Scheme.AdicCoefficientDatum A)
  (M : ∀ n : ℕ, PbcWitnessAmbient T d n)
  (hM : ∀ n : ℕ, DerivedCategory.TStructure.t.plus
    ((finiteCoefficientRealization T (PbcQuotient d n)).mapDerivedCategory.obj (M n)))
  (W : ∀ n : ℕ, Scheme.EtaleOriginWitness T (PbcQuotient d n)
    ⟨(finiteCoefficientRealization T (PbcQuotient d n)).mapDerivedCategory.obj (M n), hM n⟩)
  (rho : ∀ (m n : ℕ) (h : n ≤ m),
    (normalizedOriginReduction (Scheme.ProEt.topology T) d m n h).obj (M m) ≅ M n)

end AlgebraicGeometry.ProEtale
