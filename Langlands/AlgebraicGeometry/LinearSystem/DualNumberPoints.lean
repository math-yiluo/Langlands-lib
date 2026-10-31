import Langlands.AlgebraicGeometry.Picard.LineBundleSectionVanishingProof
import Langlands.AlgebraicGeometry.Picard.PointTangentSeparation
import Mathlib.RingTheory.DualNumber

/-! # Points of `Spec K` and `Spec K[ε]` in an open

The spectra of a field and of its dual numbers have a single point. Hence a rational point
whose closed point lies in an open lies in it everywhere, and so does every `K[ε]`-point
restricting to it.
-/

universe u

open CategoryTheory AlgebraicGeometry Langlands.AlgebraicGeometry.Picard

namespace Langlands.AlgebraicGeometry.LinearSystem

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- Every prime ideal of the dual numbers is the maximal ideal `(ε)`. -/
lemma dualNumber_prime_eq_maximalIdeal (P : Ideal (DualNumber K)) [P.IsPrime] :
    P = IsLocalRing.maximalIdeal (DualNumber K) := by
  refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) ?_
  rw [DualNumber.maximalIdeal_eq_span_singleton_eps, Ideal.span_le, Set.singleton_subset_iff]
  exact Ideal.IsPrime.mem_of_pow_mem ‹_› 2
    (by rw [pow_two, DualNumber.eps_mul_eps]; exact P.zero_mem)

/-- The spectrum of the dual numbers has a single point. -/
lemma subsingleton_spec_dualNumber : Subsingleton (Spec (CommRingCat.of (DualNumber K))) := by
  change Subsingleton (PrimeSpectrum (DualNumber K))
  exact subsingleton_primeSpectrum_dualNumber K

/-- A rational point whose closed point lies in an open lies in it everywhere. -/
lemma forall_mem_of_mem {x : Spec (CommRingCat.of K) ⟶ X} {U : X.Opens}
    (hx : x (IsLocalRing.closedPoint K) ∈ U) : ∀ τ, x τ ∈ U := fun τ ↦ by
  rwa [Subsingleton.elim τ (IsLocalRing.closedPoint K)]

/-- A `K[ε]`-point over a rational point in an open lies in that open. -/
lemma forall_mem_of_augmentation_comp {x : Spec (CommRingCat.of K) ⟶ X}
    {t : Spec (CommRingCat.of (DualNumber K)) ⟶ X} (ht : dualNumberAugmentation K ≫ t = x)
    {U : X.Opens} (hx : x (IsLocalRing.closedPoint K) ∈ U) : ∀ τ, t τ ∈ U := fun τ ↦ by
  have := subsingleton_spec_dualNumber (K := K)
  rw [Subsingleton.elim τ (dualNumberAugmentation K (IsLocalRing.closedPoint K))]
  rw [← ht] at hx
  exact hx

end Langlands.AlgebraicGeometry.LinearSystem
