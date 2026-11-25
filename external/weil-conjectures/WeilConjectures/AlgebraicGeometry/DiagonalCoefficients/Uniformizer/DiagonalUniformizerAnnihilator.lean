/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientDiagrams
import WeilConjectures.NumberTheory.Padics.IntegersShrinkModPow

/-! # An explicit annihilator of every uniformizer quotient

Source: diagonal tower coefficient changes, proof paragraph (1).
(blueprint: lem-diagonal-uniformizer-annihilator).
-/

@[expose] public section
set_option autoImplicit false
universe u

namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- The quotient by pi^(n+1) is killed by l^(n+1), including for ramified
extensions. A cofinal-subsystem argument is unnecessary for this annihilator.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (1).
(blueprint: lem-diagonal-uniformizer-annihilator).

Proof: l belongs to the maximal ideal of the integer ring, which is (pi).
Taking the (n+1)-st power puts l^(n+1) in (pi)^(n+1), so its image in the
quotient is zero. The same holds after lifting the quotient's universe. -/
theorem diagonalUniformizer_annihilator
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) (n : ℕ) :
    ((l ^ (n + 1) : ℕ) : ULift.{u + 1} (completedResidue l E π n)) = 0 := by
  have hl : (l : PadicAlgCl.integers l E) ∈ Ideal.span {π} := by
    rw [hπ]
    exact PadicAlgCl.natCast_mem_maximalIdeal_integers l E.1
  have hp := Ideal.pow_mem_pow hl (n + 1)
  have hq : (Ideal.Quotient.mk (Ideal.span {π} ^ (n + 1)))
      ((l : PadicAlgCl.integers l E) ^ (n + 1)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hp
  apply ULift.ext
  change ((l ^ (n + 1) : ℕ) : completedResidue l E π n) = 0
  simpa only [map_pow, map_natCast, Nat.cast_pow] using hq

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
