/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.KrullDimension

/-!
# Relative global complete intersections

Source: Stacks Project, Algebra, Definition Tag 00SP
(blueprint: theorem-finite-etale-covers-proper-henselian--2).
-/

@[expose] public section

namespace Algebra

/-- A ring map is a relative global complete intersection when it has a finite
polynomial presentation whose nonempty fibres all have the expected dimension.
If `c > n`, this forces every fibre to be empty.
Source: Stacks Project, Algebra, Definition Tag 00SP
(blueprint: theorem-finite-etale-covers-proper-henselian--2).
-/
def IsRelativeGlobalCompleteIntersection {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  ∃ (n c : ℕ) (relations : Fin c → MvPolynomial (Fin n) R),
    ∃ _e : (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range relations)) ≃ₐ[R] S,
      ∀ (p : Ideal R) (_hp : p.IsPrime),
        letI : p.IsPrime := _hp
        Nontrivial
            (p.Fiber (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range relations))) →
          c ≤ n ∧
            topologicalKrullDim
                (PrimeSpectrum
                  (p.Fiber (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range relations)))) =
              (n - c : ℕ)

end Algebra
