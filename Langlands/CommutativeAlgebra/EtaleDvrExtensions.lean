import Langlands.CommutativeAlgebra.DVRAlgebraicBaseChange
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Smooth.Flat

/-! # Local essentially etale extensions of a DVR -/

noncomputable section

namespace Langlands.CommutativeAlgebra.EtaleDvrExtensions

open IsLocalRing
open DVRAlgebraicBaseChange

section PowerUnit

variable {S : Type*} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]

/-- A Noetherian local ring with principal maximal ideal has power-unit
factorizations, without an a priori reducedness assumption. -/
theorem eq_zero_or_pow_mul_unit (t : S)
    (hm : maximalIdeal S = Ideal.span {t}) (y : S) :
    y = 0 ∨ ∃ (j : ℕ) (u : S), IsUnit u ∧ y = t ^ j * u := by
  let e := IsLocalization.atUnits S (maximalIdeal S).primeCompl
    (S := Localization.AtPrime (maximalIdeal S))
    fun x hx => (IsUnit.mem_submonoid_iff x).mpr (IsLocalRing.notMem_maximalIdeal.mp hx)
  have he (z : S) : e z = algebraMap S (Localization.AtPrime (maximalIdeal S)) z := rfl
  have ht : t ∈ maximalIdeal S := by rw [hm]; exact Ideal.mem_span_singleton_self t
  have hdiv : ∀ x ∈ maximalIdeal S, ∃ s ∉ maximalIdeal S, s * x ∈ Ideal.span {t} := by
    intro x hx
    exact ⟨1, Ideal.one_notMem _, by simpa [← hm] using hx⟩
  rcases localization_eq_zero_or_of_isNoetherianRing
    (maximalIdeal S) t ht hdiv (e y) with h0 | ⟨j, u, hu, h⟩
  · exact Or.inl (e.injective (by simpa using h0))
  · right
    refine ⟨j, e.symm u, hu.map e.symm, e.injective ?_⟩
    rw [map_mul, map_pow, e.apply_symm_apply, he]
    exact h

end PowerUnit

section LocalEtale

variable (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsLocalRing S] [Algebra R S]
  [IsLocalHom (algebraMap R S)] [Algebra.EssFiniteType R S]
  [Algebra.FormallyUnramified R S] [Module.Flat R S]

include R

/-- A flat local essentially finite type unramified algebra over a DVR is a domain. -/
theorem isDomain : IsDomain S := by
  have : IsNoetherianRing S := Algebra.EssFiniteType.isNoetherianRing R S
  have : Module.FaithfullyFlat R S := .of_flat_of_isLocalHom
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hm : maximalIdeal S = Ideal.span {algebraMap R S t} := by
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := R),
      ht.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  apply isDomain_of_forall_eq_zero_or (algebraMap R S t)
  · intro n
    rw [← map_pow]
    exact fun h => (pow_ne_zero n ht.ne_zero)
      (FaithfulSMul.algebraMap_injective R S (h.trans (map_zero _).symm))
  · exact eq_zero_or_pow_mul_unit _ hm

/-- A flat local essentially finite type unramified algebra over a DVR is a DVR. -/
theorem isDiscreteValuationRing [IsDomain S] : IsDiscreteValuationRing S := by
  have : IsNoetherianRing S := Algebra.EssFiniteType.isNoetherianRing R S
  have : Module.FaithfullyFlat R S := .of_flat_of_isLocalHom
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hm : maximalIdeal S = Ideal.span {algebraMap R S t} := by
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := R),
      ht.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  exact isDiscreteValuationRing_of_forall_eq_zero_or _
    (fun h => ht.not_isUnit (isUnit_of_map_unit (algebraMap R S) t h))
    (fun h => ht.ne_zero
      (FaithfulSMul.algebraMap_injective R S (h.trans (map_zero _).symm)))
    (eq_zero_or_pow_mul_unit _ hm)

end LocalEtale

variable {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [IsLocalHom (algebraMap R S)] [Algebra.EssFiniteType R S]
  [Algebra.FormallyUnramified R S]

/-- The image of a chosen uniformizer remains a uniformizer. -/
theorem irreducible_algebraMap
    {t : R} (ht : Irreducible t) : Irreducible (algebraMap R S t) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := R),
    ht.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]

end Langlands.CommutativeAlgebra.EtaleDvrExtensions
