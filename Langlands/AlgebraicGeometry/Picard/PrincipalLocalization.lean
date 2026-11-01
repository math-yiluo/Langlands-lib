import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.PrincipalIdealDomain

/-! # Spreading a principal localized ideal -/

namespace Langlands.AlgebraicGeometry.Picard.PrimeDivisor

set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R] (M : Submonoid R)
  (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S]

include M in
/-- A principal ideal in a localization has a generator coming from its original ideal. -/
theorem exists_numerator_generator (I : Ideal R)
    (hI : (I.map (algebraMap R S)).IsPrincipal) :
    ∃ a ∈ I, I.map (algebraMap R S) = Ideal.span {algebraMap R S a} := by
  obtain ⟨g, hg⟩ := hI
  have hgm : g ∈ I.map (algebraMap R S) := by
    rw [hg]
    exact Ideal.mem_span_singleton_self g
  obtain ⟨⟨⟨a, ha⟩, s⟩, hs⟩ := (IsLocalization.mem_map_algebraMap_iff M S).mp hgm
  refine ⟨a, ha, ?_⟩
  rw [hg, ← hs, mul_comm, Ideal.span_singleton_mul_left_unit
    (IsLocalization.map_units S s)]

/-- Finite generation gives one denominator clearing a localized containment. -/
theorem exists_denominator_of_map_le (I J : Ideal R) (hI : I.FG)
    (h : I.map (algebraMap R S) ≤ J.map (algebraMap R S)) :
    ∃ f ∈ M, ∀ x ∈ I, f * x ∈ J := by
  classical
  obtain ⟨s, hs⟩ := hI
  have hx : ∀ x ∈ s, ∃ m ∈ M, m * x ∈ J := by
    intro x hxs
    apply (IsLocalization.algebraMap_mem_map_algebraMap_iff M S J x).mp
    exact h (Ideal.mem_map_of_mem _ (hs ▸ Ideal.subset_span hxs))
  choose! m hmM hmJ using hx
  let f := ∏ x ∈ s, m x
  refine ⟨f, M.prod_mem (fun x hx ↦ hmM x hx), ?_⟩
  have hle : I ≤ J.colon (Ideal.span {f}) := by
    rw [← hs, Ideal.span_le]
    intro x hxs
    apply (Ideal.mem_colon_span_singleton).mpr
    rw [mul_comm]
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem m hxs
    change (∏ i ∈ s, m i) * x ∈ J
    rw [hc, mul_right_comm]
    exact J.mul_mem_right c (hmJ x hxs)
  intro x hxI
  simpa only [Ideal.mem_colon_span_singleton, mul_comm] using hle hxI

/-- A finitely generated ideal generated after localization is generated on one neighborhood. -/
theorem exists_principal_neighborhood (I : Ideal R) (hI : I.FG) (g : R) (hg : g ∈ I)
    (hloc : I.map (algebraMap R S) = Ideal.span {algebraMap R S g}) :
    ∃ f ∈ M, ∀ (A : Type*) [CommRing A] [Algebra R A],
      IsUnit (algebraMap R A f) →
        I.map (algebraMap R A) = Ideal.span {algebraMap R A g} := by
  have hle : I.map (algebraMap R S) ≤ (Ideal.span {g}).map (algebraMap R S) := by
    rw [Ideal.map_span, Set.image_singleton, hloc]
  obtain ⟨f, hf, hfx⟩ := exists_denominator_of_map_le M S I (Ideal.span {g}) hI hle
  refine ⟨f, hf, fun A _ _ hunit ↦ le_antisymm ?_ ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro x hxI
    have hmem := Ideal.mem_map_of_mem (algebraMap R A) (hfx x hxI)
    rw [Ideal.map_span, Set.image_singleton, map_mul] at hmem
    exact (Ideal.unit_mul_mem_iff_mem _ hunit).mp hmem
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_map_of_mem _ hg

end Langlands.AlgebraicGeometry.Picard.PrimeDivisor
