/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Pole-order valuations on a function field

Let `E` be a finite separable extension of `k⟮y⟯` with `y` transcendental over `k`. The integral
closure of `k[y]` in `E` is a Dedekind domain with fraction field `E`; its height-one primes
give a family of valuations on `E` which are trivial on `k`, have finitely many poles at each
element, and such that the elements without poles are integral over `k[y]`, so that the
coefficients of their minimal polynomials over `k⟮y⟯` are polynomials in `y`.
-/

@[expose] public section

universe v

open Polynomial IntermediateField
open scoped WithZero

namespace FrobeniusClosedBasis

variable (k : Type*) {E : Type v} [Field k] [Field E] [Algebra k E]

/-- The height-one primes of the integral closure of `k[y]` in `E` give a family of valuations on
`E`, trivial on `k`, with finitely many poles at each element, and such that the coefficients
of the minimal polynomial over `K = k⟮y⟯` of an element without poles are polynomials in `y`. -/
theorem exists_valuations_of_transcendental (y : E) (hy : Transcendental k y)
    (K : IntermediateField k E) (hK : k⟮y⟯ = K) [FiniteDimensional K E]
    [Algebra.IsSeparable K E] :
    ∃ (J : Type v) (v : J → Valuation E ℤᵐ⁰),
      (∀ j (c : k), c ≠ 0 → v j (algebraMap k E c) = 1) ∧
      (∀ f, {j | 1 < v j f}.Finite) ∧
      (∀ f, (∀ j, v j f ≤ 1) → ∀ i, ∃ q : k[X], ((minpoly K f).coeff i : E) = aeval y q) := by
  subst hK
  let : Algebra k[X] E := (aeval y).toRingHom.toAlgebra
  let y' : k⟮y⟯ := ⟨y, mem_adjoin_simple_self k y⟩
  let : Algebra k[X] k⟮y⟯ := (aeval y').toRingHom.toAlgebra
  have halg (q : k[X]) : ((algebraMap k[X] k⟮y⟯ q : k⟮y⟯) : E) = aeval y q :=
    (aeval_algHom_apply (IntermediateField.val _) y' q).symm
  have halg' (q : k[X]) : algebraMap k[X] E q = aeval y q := rfl
  have : IsScalarTower k[X] k⟮y⟯ E :=
    IsScalarTower.of_algebraMap_eq fun q ↦ (halg q).symm
  have : FaithfulSMul k[X] k⟮y⟯ :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 fun a b hab ↦
      transcendental_iff_injective.1 hy (by rw [← halg, ← halg, hab])
  have : IsFractionRing k[X] k⟮y⟯ := IsFractionRing.of_field _ _ fun z ↦ by
    obtain ⟨r, s, hrs⟩ := (mem_adjoin_simple_iff k (z : E)).1 z.2
    exact ⟨r, s, Subtype.ext (by rw [hrs, IntermediateField.coe_div, halg, halg])⟩
  have := integralClosure.isDedekindDomain k[X] k⟮y⟯ E
  have := integralClosure.isFractionRing_of_finite_extension (A := k[X]) k⟮y⟯ E
  refine ⟨IsDedekindDomain.HeightOneSpectrum (integralClosure k[X] E), fun P ↦ P.valuation E,
    fun P c hc ↦ ?_, fun f ↦ IsDedekindDomain.HeightOneSpectrum.Support.finite _ f,
    fun f hf i ↦ ?_⟩
  · have hle (a : E) (ha : IsIntegral k[X] a) : P.valuation E a ≤ 1 :=
      P.valuation_le_one ⟨a, ha⟩
    have hc' (c : k) : IsIntegral k[X] (algebraMap k E c) := by
      rw [← aeval_C y c, ← halg']
      exact isIntegral_algebraMap
    have h2 := hle _ (hc' c⁻¹)
    rw [map_inv₀, Valuation.map_inv] at h2
    have hpos : 0 < P.valuation E (algebraMap k E c) := by
      rw [Valuation.pos_iff]
      simpa using hc
    exact le_antisymm (hle _ (hc' c)) ((inv_le_one₀ hpos).1 h2)
  · obtain ⟨a, rfl⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one E f hf
    have ha : IsIntegral k[X] (algebraMap (integralClosure k[X] E) E a) := a.2
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' k⟮y⟯ ha, coeff_map]
    exact ⟨_, halg _⟩

end FrobeniusClosedBasis
