module

public import StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.PoleReduction

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Eliminating degree-prime ramification: Laurent coefficients and the constant numerator

Uniformizers under weakly unramified extensions, the Artin--Schreier extension adjoining a root of
`X ^ p - X - π ^ (-n) a`, constant numerators from coefficient lifts, the
trivial/unramified/totally ramified trichotomy for a minimal numerator, and elements outside the
perfect core.
-/

@[expose] public section

open Polynomial
open nonZeroDivisors
open WithZero

open scoped TensorProduct

attribute [local instance] FractionRing.liftAlgebra
attribute [local instance] Ideal.Quotient.field

universe uA uB uC uK uL uM uK₁

namespace IsDiscreteValuationRing

/-- **A uniformizer remains a uniformizer under a weakly unramified DVR extension.**

Public because the iteration that discharges the antecedent of
`exists_isGalois_totallyRamified_isWeakSolution_of_charP_of_finiteSupport` needs it: that
antecedent is supplied by a weakly unramified base change
(`Stacks.EppTheorem.EppCondition.exists_finiteEtale_forall_exists_pow_eq_algebraMap`), and the
  layer's
finite set and depth are built from an Artin--Schreier presentation over a uniformizer of the
base, so closing the loop requires knowing the uniformizer — and hence the presentation — is
unchanged by that base change. -/
theorem irreducible_algebraMap_of_isWeaklyUnramified
    {A B : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B]
    (hweak : IsWeaklyUnramified A B) {π : A} (hπ : Irreducible π) :
    Irreducible (algebraMap A B π) := by
  apply (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
  have h := (ramificationIndex_characterization A B).2.1
  rw [show ramificationIndex A B = 1 from hweak, pow_one,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ,
    Ideal.map_span, Set.image_singleton] at h
  exact h.symm

/-- If the coefficients of a finite expansion lift from the base modulo the pole bound, then its
Laurent principal part has a numerator in the base DVR — and that numerator is the *visible* sum
`∑ i < n, lift i * π ^ i` of the supplied lifts.

The lifts are arguments rather than existential witnesses so that the numerator is a term the
caller can compute with.  What a caller needs from it is its residue, which by
`residue_sum_mul_uniformizer_pow` is the residue of `lift 0` alone; that is what turns knowledge
about the zeroth coefficient into a `p`-th root of the numerator's residue.
`exists_constant_numerator_of_coefficients_lift` is the existential wrapper. -/
theorem eq_constant_numerator_of_coefficients_lift
    {A B L : Type*} [CommRing A] [CommRing B] [Field L]
    [Algebra A B] [Algebra A L] [Algebra B L] [IsScalarTower A B L]
    (π : A) (ht : algebraMap A L π ≠ 0) (n : ℕ)
    (coeff : ℕ → B) (b : B) (ξ : L) (lift : ℕ → A)
    (hexp : algebraMap A L π ^ n * ξ =
      algebraMap B L ((∑ i ∈ Finset.range n, coeff i * algebraMap A B π ^ i) +
        algebraMap A B π ^ n * b))
    (hlift : ∀ i ∈ Finset.range n,
      coeff i - algebraMap A B (lift i) ∈ Ideal.span {algebraMap A B π ^ n}) :
    ∃ b' : B, ξ = (algebraMap A L π)⁻¹ ^ n *
      algebraMap A L (∑ i ∈ Finset.range n, lift i * π ^ i) + algebraMap B L b' := by
  classical
  have hc : ∀ i ∈ Finset.range n, ∃ c : B,
      coeff i = algebraMap A B (lift i) + algebraMap A B π ^ n * c := fun i hi => by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (hlift i hi)
    exact ⟨c, by linear_combination hc⟩
  choose! c hc using hc
  refine ⟨(∑ i ∈ Finset.range n, c i * algebraMap A B π ^ i) + b, ?_⟩
  apply (mul_left_cancel₀ (pow_ne_zero n ht))
  rw [hexp]
  simp only [map_add, map_sum, map_mul, map_pow, mul_add, Finset.mul_sum,
    ← IsScalarTower.algebraMap_apply]
  rw [← add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [hc i hi]
  simp only [map_add, map_mul, map_pow, ← IsScalarTower.algebraMap_apply]
  have hcancel : algebraMap A L π ^ n * (algebraMap A L π)⁻¹ ^ n = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ ht, one_pow]
  linear_combination -(algebraMap A L (lift i) * algebraMap A L π ^ i) * hcancel

end IsDiscreteValuationRing
