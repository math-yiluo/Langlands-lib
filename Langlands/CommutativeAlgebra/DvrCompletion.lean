import Langlands.CommutativeAlgebra.DVRAlgebraicBaseChange
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Adic completion of a discrete valuation ring -/

noncomputable section

open IsLocalRing

namespace Langlands.CommutativeAlgebra

section SeparatedLocalRing

variable {S : Type*} [CommRing S] [IsLocalRing S] [IsHausdorff (maximalIdeal S) S]

/-- In a separated local ring with maximal ideal `(t)`, every nonzero element is a
unit times a power of `t`. -/
theorem eq_zero_or_pow_mul_unit_of_maximalIdeal_eq_span {t : S}
    (ht : maximalIdeal S = Ideal.span {t}) (x : S) :
    x = 0 ∨ ∃ (n : ℕ) (u : S), IsUnit u ∧ x = t ^ n * u := by
  classical
  by_cases hx : x = 0
  · exact Or.inl hx
  right
  have hex : ∃ n : ℕ, x ∉ maximalIdeal S ^ n := by
    by_contra! h
    apply hx
    apply IsHausdorff.haus' (I := maximalIdeal S) x
    simpa only [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top] using h
  have hpos : Nat.find hex ≠ 0 := by
    intro hz
    have hn := Nat.find_spec hex
    rw [hz, pow_zero, Ideal.one_eq_top] at hn
    exact hn Submodule.mem_top
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have hmem : x ∈ maximalIdeal S ^ n := by
    simpa using Nat.find_min hex (show n < Nat.find hex by rw [hn]; exact Nat.lt_succ_self _)
  have hnot : x ∉ maximalIdeal S ^ (n + 1) := by
    have h := Nat.find_spec hex
    rw [hn] at h
    exact h
  rw [ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmem
  obtain ⟨u, hu⟩ := hmem
  refine ⟨n, u, ?_, by rw [← hu, mul_comm]⟩
  by_contra hnu
  have hum : u ∈ maximalIdeal S := (mem_maximalIdeal u).mpr hnu
  rw [ht, Ideal.mem_span_singleton'] at hum
  obtain ⟨c, hc⟩ := hum
  apply hnot
  rw [ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  exact ⟨c, by rw [← hu, ← hc, pow_succ]; ac_rfl⟩

/-- A separated local ring with a regular generator of its maximal ideal is a DVR. -/
theorem isDomain_and_isDiscreteValuationRing_of_maximalIdeal_eq_span {t : S}
    (ht : maximalIdeal S = Ideal.span {t}) (hreg : IsSMulRegular S t) :
    ∃ _ : IsDomain S, IsDiscreteValuationRing S := by
  have hpow (n : ℕ) : t ^ n ≠ 0 := by
    induction n with
    | zero => simpa only [pow_zero] using (one_ne_zero : (1 : S) ≠ 0)
    | succ n ih =>
        intro h
        exact ih (hreg (show t • t ^ n = t • 0 by
          simpa only [smul_eq_mul, mul_zero, ← pow_succ'] using h))
  have h := eq_zero_or_pow_mul_unit_of_maximalIdeal_eq_span ht
  have : IsDomain S := DVRAlgebraicBaseChange.isDomain_of_forall_eq_zero_or t hpow h
  refine ⟨inferInstance, DVRAlgebraicBaseChange.isDiscreteValuationRing_of_forall_eq_zero_or t
    ((mem_maximalIdeal t).mp (ht ▸ Ideal.mem_span_singleton_self t : t ∈ maximalIdeal S)) ?_ h⟩
  simpa using hpow 1

end SeparatedLocalRing

namespace DvrCompletion

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

local notation "R̂" => AdicCompletion (maximalIdeal R) R

/-- A uniformizer generates the maximal ideal after completion. -/
theorem maximalIdeal_eq_span {t : R} (ht : Irreducible t) :
    maximalIdeal R̂ = Ideal.span {algebraMap R R̂ t} := by
  rw [AdicCompletion.maximalIdeal_eq_map, ht.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]

/-- The maximal-ideal adic completion of a DVR is a domain and a DVR. -/
theorem isDomain_and_isDiscreteValuationRing : ∃ _ : IsDomain R̂, IsDiscreteValuationRing R̂ := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hreg : IsSMulRegular R t := fun _ _ h => mul_left_cancel₀ ht.ne_zero h
  exact isDomain_and_isDiscreteValuationRing_of_maximalIdeal_eq_span
    (maximalIdeal_eq_span R ht) (hreg.of_flat (S := R̂))

/-- A DVR is faithfully flat in its maximal-ideal adic completion. -/
theorem faithfullyFlat : Module.FaithfullyFlat R R̂ :=
  Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- The residue map of a DVR to its completion is an isomorphism of residue fields. -/
def residueEquiv : ResidueField R ≃+* ResidueField R̂ :=
  RingEquiv.ofBijective (ResidueField.map (algebraMap R R̂))
    (AdicCompletion.residueField_map_bijective R)

end DvrCompletion

end Langlands.CommutativeAlgebra
