import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

open scoped BigOperators

namespace Langlands.Algebra

/-- A map into an Artinian ring sends some element of an ideal to a unit
whenever the image ideal is the whole target. -/
theorem exists_isUnit_of_map_eq_top_of_artinian
    {R A : Type*} [CommRing R] [CommRing A] [IsArtinianRing A]
    (φ : R →+* A) (I : Ideal R) (hI : I.map φ = ⊤) :
    ∃ r ∈ I, IsUnit (φ r) := by
  classical
  by_contra h
  push Not at h
  have hs : {M : Ideal A | M.IsMaximal}.Finite :=
    IsArtinianRing.setOfPred_isMaximal_finite A
  have hsub : (I : Set R) ⊆ ⋃ M ∈ {M : Ideal A | M.IsMaximal},
      (M.comap φ : Set R) := by
    intro r hr
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal
      (Ideal.span {φ r}) (Ideal.span_singleton_ne_top (h r hr))
    exact Set.mem_iUnion.mpr ⟨M, Set.mem_iUnion.mpr ⟨hM,
      hle (Ideal.subset_span (Set.mem_singleton _))⟩⟩
  obtain ⟨M, hM, hle⟩ := (Ideal.subset_union_prime_finite hs
    (⊥ : Ideal A) (⊥ : Ideal A) (fun M hM _ _ =>
      (Ideal.IsMaximal.isPrime hM).comap φ)).mp hsub
  have htop : (⊤ : Ideal A) ≤ M := by
    rw [← hI]
    exact Ideal.map_le_iff_le_comap.mpr hle
  exact hM.ne_top (top_le_iff.mp htop)

/-- Prime avoidance for arbitrary maps into an algebra integral over a field.
No finite generation hypothesis is imposed on either ring. -/
theorem exists_isUnit_of_map_eq_top_of_integral_field
    {k R A : Type*} [Field k] [CommRing R] [CommRing A]
    [Algebra k A] [Algebra.IsIntegral k A]
    (φ : R →+* A) (I : Ideal R) (hI : I.map φ = ⊤) :
    ∃ r ∈ I, IsUnit (φ r) := by
  classical
  have h1 : (1 : A) ∈ Submodule.span A (φ '' (I : Set R)) := by
    change (1 : A) ∈ I.map φ
    rw [hI]
    trivial
  obtain ⟨c, t, ht, _, hsum⟩ := Submodule.mem_span_iff_exists_finset_subset.mp h1
  let B : Subalgebra k A := Algebra.adjoin k ((t : Set A) ∪ c '' (t : Set A))
  have hb (a : A) (ha : a ∈ t) : a ∈ B :=
    Algebra.subset_adjoin (Or.inl ha)
  have hc (a : A) (ha : a ∈ t) : c a ∈ B :=
    Algebra.subset_adjoin (Or.inr ⟨a, ha, rfl⟩)
  have : Module.Finite k B := Algebra.finite_adjoin_of_finite_of_isIntegral
    (t.finite_toSet.union (t.finite_toSet.image c))
    (fun _ _ => Algebra.IsIntegral.isIntegral _)
  have : IsArtinianRing B := IsArtinianRing.of_finite k B
  let S : Subring R := B.toSubring.comap φ
  let ψ : S →+* B := (φ.comp S.subtype).codRestrict B.toSubring (fun r => r.property)
  let J : Ideal S := I.comap S.subtype
  let b : t → B := fun a => ⟨a, hb a a.property⟩
  let d : t → B := fun a => ⟨c a, hc a a.property⟩
  have hbJ (a : t) : b a ∈ J.map ψ := by
    obtain ⟨r, hr, heq⟩ := ht a.property
    let r' : S := ⟨r, show φ r ∈ B from heq ▸ hb a a.property⟩
    have hr' : r' ∈ J := hr
    convert Ideal.mem_map_of_mem ψ hr' using 1
    exact Subtype.ext heq.symm
  have hsumB : ∑ a : t, d a * b a = 1 := by
    apply Subtype.val_injective
    change B.val (∑ a : t, d a * b a) = B.val 1
    rw [map_sum]
    change (∑ a : t, c a * (a : A)) = 1
    rw [Finset.sum_coe_sort t (fun a : A => c a * a)]
    simpa only [smul_eq_mul] using hsum
  have hJ : J.map ψ = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    rw [← hsumB]
    exact Submodule.sum_mem _ (fun a _ => Ideal.mul_mem_left _ (d a) (hbJ a))
  obtain ⟨r, hr, hu⟩ := exists_isUnit_of_map_eq_top_of_artinian ψ J hJ
  exact ⟨r, hr, hu.map B.val.toRingHom⟩

/-- A chosen element of the original ideal that becomes a unit in an
integral algebra over a field. -/
noncomputable def integralFieldUnitWitness
    {k R A : Type*} [Field k] [CommRing R] [CommRing A]
    [Algebra k A] [Algebra.IsIntegral k A]
    (φ : R →+* A) (I : Ideal R) (hI : I.map φ = ⊤) :
    {r : R // r ∈ I ∧ IsUnit (φ r)} :=
  ⟨Classical.choose (exists_isUnit_of_map_eq_top_of_integral_field (k := k) φ I hI),
    Classical.choose_spec (exists_isUnit_of_map_eq_top_of_integral_field (k := k) φ I hI)⟩

end Langlands.Algebra
