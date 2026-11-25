/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.FiniteTorsionConstructibility
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic

/-!
# Intrinsic finite-torsion constructibility without a global base datum
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The intrinsic bounded constructibility condition, independent of a chosen global
finite-field datum. This is exactly the cohomological predicate in
`finiteTorsionConstructible`, with its unused global parameters removed.
The quotient coefficient ring and its chosen uniformizer remain the recorded ones. -/
noncomputable def intrinsicFiniteTorsionConstructible
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n) (Y : Scheme.{u}) :
    ObjectProperty (proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n)) :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  fun K ↦
    Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules Y
        (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E n))) i).obj K)} ∧
      ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf Y
        (Padic.coefficientExtensionRing l E n)
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules Y
            (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E n))) i).obj K)

end AlgebraicGeometry.Scheme
