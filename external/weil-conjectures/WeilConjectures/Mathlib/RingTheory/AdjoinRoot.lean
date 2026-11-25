/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.AdjoinRoot

/-!
# The quotient of a polynomial ring by a monic polynomial

For a monic `f : R[X]` of degree `n`, the algebra `R[X] ⧸ (f) = AdjoinRoot f` is free over `R`
with basis `1, X, …, Xⁿ⁻¹` (mathlib's `AdjoinRoot.powerBasis'`), hence finite, and its reduction
modulo an ideal `I` of `R` is `(R ⧸ I)[X] ⧸ (f mod I)` (mathlib's `AdjoinRoot.quotEquivQuotMap`).

## Main statements

- `Polynomial.Monic.exists_powerBasis_adjoinRoot`: the three facts above, as one statement.
-/

@[expose] public section

open Polynomial

namespace Polynomial.Monic

/-- Let `f : R[X]` be monic of degree `n`. Then `R[X] ⧸ (f)` has an `R`-basis given by the
classes of `1, X, …, Xⁿ⁻¹`; in particular it is a finite free `R`-module, and for every ideal `I`
of `R`, its reduction modulo `I` is `(R ⧸ I)[X] ⧸ (f mod I)`, by an isomorphism sending the class
of `g` to the class of `g mod I`.
(blueprint: `lem-weil-pbc-monic-quotient-free`) -/
@[stacks 04GG]
theorem exists_powerBasis_adjoinRoot {R : Type*} [CommRing R] {f : R[X]} (hf : f.Monic) :
    (∃ pb : PowerBasis R (AdjoinRoot f), pb.gen = AdjoinRoot.root f ∧ pb.dim = f.natDegree) ∧
      Module.Free R (AdjoinRoot f) ∧ Module.Finite R (AdjoinRoot f) ∧
      ∀ I : Ideal R, ∃ e : (AdjoinRoot f ⧸ I.map (AdjoinRoot.of f)) ≃ₐ[R]
        (R ⧸ I)[X] ⧸ Ideal.span {f.map (Ideal.Quotient.mk I)}, ∀ g : R[X],
          e (Ideal.Quotient.mk _ (AdjoinRoot.mk f g)) =
            Ideal.Quotient.mk _ (g.map (Ideal.Quotient.mk I)) :=
  ⟨⟨AdjoinRoot.powerBasis' hf, rfl, rfl⟩, hf.free_adjoinRoot, hf.finite_adjoinRoot,
    fun I ↦ ⟨AdjoinRoot.quotEquivQuotMap f I, fun g ↦ AdjoinRoot.quotEquivQuotMap_apply_mk f g I⟩⟩

end Polynomial.Monic
