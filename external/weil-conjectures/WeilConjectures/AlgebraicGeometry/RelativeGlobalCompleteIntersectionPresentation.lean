/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RelativeGlobalCompleteIntersection

/-!
# The relative global complete intersection condition for specified equations

Source: Stacks Project, Algebra, Definition 00SP
(blueprint: theorem-finite-etale-covers-proper-henselian--2).
The ring-map notion is `Algebra.IsRelativeGlobalCompleteIntersection` in the imported module;
this module supplies the specified-presentation notion in the same definition.
-/

@[expose] public section

universe u

namespace Algebra

/-- The specified quotient presentation is a relative global complete intersection when every
nonempty fibre has dimension the number of variables minus the number of equations.
The inequality prevents natural-number subtraction from admitting negative dimensions.
Source: Stacks Project, Algebra, Definition 00SP
(blueprint: theorem-finite-etale-covers-proper-henselian--2). -/
def IsRelativeGlobalCompleteIntersectionPresentation {R : Type u} [CommRing R]
    {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) R) : Prop :=
  ∀ (p : Ideal R) [p.IsPrime],
    Nontrivial (p.Fiber (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f))) →
      c ≤ n ∧
        topologicalKrullDim
          (PrimeSpectrum (p.Fiber (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))) =
            (n - c : ℕ)

end Algebra
