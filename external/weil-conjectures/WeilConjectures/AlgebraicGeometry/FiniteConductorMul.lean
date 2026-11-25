/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.Maps

/-! The ideal-power form of the finite conductor statement.

Source: literature/stacks-project/varieties.tex, Varieties Lemma 09N2.
(blueprint: semilocal-dim-one-conductor-power-mul)
-/
@[expose] public section
universe u v

/-- If a finite intermediate subalgebra has conductor exponent `r`, every element of
`(J(B)A)^r` multiplied by an element of `A` comes from `B`. The explicit hypothesis
`hconductor` states the base ideal power conductor property. The proof extends it
to the mapped ideal by span induction.

(blueprint: semilocal-dim-one-conductor-power-mul)

Source: literature/stacks-project/varieties.tex, Varieties Lemma 09N2.

Proof: rewrite the mapped ideal power as the map of the base ideal power. Induct on
membership in the span defining that map. The conductor hypothesis handles a mapped
base element; zero and sums are preserved by the algebra map. For a scalar multiple,
absorb the scalar into the multiplier in A and commute the factors.

The original statement was false without `hconductor`: r = 0 and z = 1 would force
A to equal the image of B. This explicit conductor hypothesis is retained from the
finite conductor theorem at the caller.
-/
/- STATEMENT-DISPUTED: the original statement omitted the conductor property for r.
At r = 0 and z = 1 it would force every element of A to come from B.
The corrected statement below makes the source's suitable-exponent condition explicit. -/
theorem Subalgebra.exists_base_mul_mem_of_mem_map_jacobson_pow
    {B : Type u} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Finite (MaximalSpectrum B)] (hdim : ringKrullDim B = 1)
    {K : Type v} [Field K] [Algebra B K] [IsFractionRing B K]
    (A : Subalgebra B K) [Module.Finite B A] [IsFractionRing A K]
    {r : ℕ}
    (hconductor : ∀ b : B, b ∈ (Ideal.jacobson (⊥ : Ideal B)) ^ r →
      ∀ a : A, ∃ c : B, algebraMap B K c = algebraMap B K b * (a : K))
    (z : A)
    (hz : z ∈ (Ideal.map (algebraMap B A) (Ideal.jacobson (⊥ : Ideal B))) ^ r)
    (a : A) : ∃ c : B, algebraMap B K c = (z : K) * (a : K) := by
  have _hdim := hdim
  rw [← Ideal.map_pow] at hz
  have h : ∀ a : A, ∃ c : B, algebraMap B K c = (z : K) * (a : K) := by
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, rfl⟩ := hx
      intro a
      simpa using hconductor b hb a
    | zero =>
      intro a
      exact ⟨0, by simp⟩
    | add x y hx hy ihx ihy =>
      intro a
      obtain ⟨c, hc⟩ := ihx a
      obtain ⟨d, hd⟩ := ihy a
      exact ⟨c + d, by simpa [add_mul] using congrArg₂ (· + ·) hc hd⟩
    | smul t x hx ih =>
      intro a
      obtain ⟨c, hc⟩ := ih (t * a)
      exact ⟨c, by simpa [smul_eq_mul, mul_left_comm, mul_assoc] using hc⟩
  exact h a
