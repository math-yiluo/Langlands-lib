import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! # Discrete valuation rings at the generic points of a principal fibre -/

open IsLocalRing

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

/-- A normal domain localization at a prime minimal over a regular principal ideal
of a Noetherian ring is a DVR. -/
theorem isDiscreteValuationRing_atPrime_of_minimal_principal {A : Type*} [CommRing A]
    [IsNoetherianRing A] {a : A} (ha : a ∈ nonZeroDivisors A)
    (p : Ideal A) [p.IsPrime] [IsDomain (Localization.AtPrime p)]
    [IsIntegrallyClosed (Localization.AtPrime p)] (hp : p ∈ (Ideal.span {a}).minimalPrimes) :
    IsDiscreteValuationRing (Localization.AtPrime p) := by
  let D := Localization.AtPrime p
  have hheight := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {a}) p hp
  have : Ring.KrullDimLE 1 D := Ring.krullDimLE_iff.mpr (by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p]
    exact WithBot.coe_le_coe.mpr hheight)
  have : Ring.DimensionLEOne D := ⟨fun hne hPrime => hPrime.isMaximal_of_ne_bot hne⟩
  have : IsDedekindRing D := {}
  have hm : algebraMap A D a ∈ maximalIdeal D :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff D p a).mpr
      (hp.le (Ideal.mem_span_singleton_self a))
  have haD : algebraMap A D a ≠ 0 :=
    nonZeroDivisors.ne_zero (IsLocalization.nonZeroDivisors_le_comap p.primeCompl D ha)
  have hnF : ¬IsField D := by
    rw [isField_iff_maximalIdeal_eq]
    exact fun h => haD (Ideal.mem_bot.mp (h ▸ hm))
  exact ((IsDiscreteValuationRing.TFAE D hnF).out 3 1).mp (inferInstance : IsDedekindDomain D)

/-- The quotient of a DVR by a nonzero nonunit is reduced exactly when the element
is a uniformizer. -/
theorem isReduced_quotient_span_singleton_iff_irreducible {D : Type*} [CommRing D]
    [IsDomain D] [IsDiscreteValuationRing D] {x : D} (hx : x ≠ 0) (hxunit : ¬IsUnit x) :
    IsReduced (D ⧸ Ideal.span {x}) ↔ Irreducible x := by
  constructor
  · intro hred
    have hrad := (Ideal.isRadical_iff_quotient_reduced (Ideal.span {x})).mpr hred
    obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible D
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx ht
    have hpow : t ^ n ∈ Ideal.span {x} := by
      rw [← Ideal.unit_mul_mem_iff_mem _ u.isUnit, ← hu]
      exact Ideal.mem_span_singleton_self x
    apply (IsDiscreteValuationRing.irreducible_iff_uniformizer x).mpr
    refine le_antisymm ?_ ((maximalIdeal D).span_singleton_le_iff_mem.mpr
      ((mem_maximalIdeal x).mpr hxunit))
    rw [ht.maximalIdeal_eq, Ideal.span_singleton_le_iff_mem]
    exact hrad (Ideal.mem_radical_iff.mpr ⟨n, hpow⟩)
  · intro h
    rw [← h.maximalIdeal_eq]
    infer_instance

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
