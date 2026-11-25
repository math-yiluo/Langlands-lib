/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.CharP.Algebra

/-! # Prime-power units over the fixed finite-field base

A prime different from the characteristic is invertible on every scheme over the
fixed algebraic closure. The statement needs no coefficient extension or purity setting.
Source: finite coefficient conventions (blueprint: lem-sp-finite-field-prime-power-unit).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- Every power of a prime different from the characteristic is a unit on a k-scheme.
Source: finite coefficient conventions, the invertibility hypothesis in the reduction
compatibilities proof (blueprint: lem-sp-finite-field-prime-power-unit).

Proof: the cardinality of the finite base field determines its characteristic p.
Its algebraic closure has characteristic p as well. The image of the other prime ell
in that field is nonzero and hence a unit. Map this unit through the structure map on
global sections and raise it to the n-th power. This also covers n=0 and empty schemes. -/
theorem finiteFieldPrimePower_isUnit (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p) (n : ℕ) {T : Scheme.{u}}
    (a : T ⟶ Spec (.of D.k)) : IsUnit ((ell ^ n : ℕ) : Γ(T, ⊤)) := by
  let : Fintype D.k₀ := Fintype.ofFinite _
  have : Fact D.p.Prime := ⟨D.prime⟩
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card, D.card_base, D.cardinality_eq])
  have : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have hl : IsUnit (ell : D.k) :=
    isUnit_iff_ne_zero.mpr
      (CharP.cast_ne_zero_of_ne_of_prime _ (Fact.out : ell.Prime) hEll.symm)
  let f := (Scheme.ΓSpecIso (CommRingCat.of D.k)).inv ≫ a.appTop
  simpa only [map_natCast, Nat.cast_pow] using (hl.map f.hom).pow n

end AlgebraicGeometry.ProEtale
