import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.Sober

/-!
# Nagata's openness criterion

Matsumura, *Commutative Ring Theory*, Theorem 24.2: for a Noetherian ring `A`, a subset
`U ⊆ Spec A` is open if it is stable under generization and, for every `p ∈ U`, the set
`U ∩ V(p)` contains a nonempty open subset of `V(p)`.
-/

open TopologicalSpace

namespace Langlands.Algebra

/-- A closed subset of a Noetherian space is a finite union of closed irreducible subsets,
none of which is contained in the union of the others. -/
theorem exists_finset_isClosed_isIrreducible_irredundant {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] {C : Set X} (hC : IsClosed C) :
    ∃ S : Finset (Set X), (∀ t ∈ S, IsClosed t ∧ IsIrreducible t) ∧ C = (⋃ t ∈ S, t) ∧
      ∀ T ∈ S, ¬T ⊆ ⋃ t ∈ S.erase T, t := by
  classical
  have hex : ∃ n, ∃ S : Finset (Set X), S.card = n ∧
      (∀ t ∈ S, IsClosed t ∧ IsIrreducible t) ∧ C = ⋃ t ∈ S, t := by
    obtain ⟨S, hSf, hSc, hSi, hSU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hC
    refine ⟨_, hSf.toFinset, rfl, fun t ht =>
      ⟨hSc t (hSf.mem_toFinset.mp ht), hSi t (hSf.mem_toFinset.mp ht)⟩, ?_⟩
    rw [hSU, Set.sUnion_eq_biUnion]
    simp
  obtain ⟨S, hcard, hS, hCS⟩ := Nat.find_spec hex
  refine ⟨S, hS, hCS, fun T hT hsub => ?_⟩
  have hlt : (S.erase T).card < Nat.find hex := hcard ▸ Finset.card_erase_lt_of_mem hT
  refine Nat.find_min hex hlt ⟨S.erase T, rfl, fun t ht => hS t (Finset.mem_of_mem_erase ht), ?_⟩
  rw [hCS]
  refine subset_antisymm (Set.iUnion₂_subset fun t ht x hxt => ?_)
    (Set.iUnion₂_subset fun t ht => Set.subset_iUnion₂ (s := fun t (_ : t ∈ S) => t) t
      (Finset.mem_of_mem_erase ht))
  by_cases h : t = T
  · subst h
    exact hsub hxt
  · exact Set.mem_iUnion₂.mpr ⟨t, Finset.mem_erase.mpr ⟨h, ht⟩, hxt⟩

/-- **Nagata's openness criterion** (Matsumura, Theorem 24.2). Let `A` be a Noetherian ring
and `U ⊆ Spec A` stable under generization. If for every `p ∈ U` there is `f ∉ p` with
`V(p) ∩ D(f) ⊆ U`, then `U` is open. -/
theorem isOpen_of_stableUnderGeneralization_of_forall_exists {A : Type*} [CommRing A]
    [IsNoetherianRing A] {U : Set (PrimeSpectrum A)} (hU : StableUnderGeneralization U)
    (h : ∀ p ∈ U, ∃ f : A, f ∉ p.asIdeal ∧
      ∀ q : PrimeSpectrum A, p ≤ q → f ∉ q.asIdeal → q ∈ U) :
    IsOpen U := by
  rw [← isClosed_compl_iff, ← closure_subset_iff_isClosed]
  obtain ⟨S, hS, hCS, hirr⟩ :=
    exists_finset_isClosed_isIrreducible_irredundant (isClosed_closure (s := Uᶜ))
  rw [hCS]
  refine Set.iUnion₂_subset fun T hT => ?_
  obtain ⟨hTc, hTi⟩ := hS T hT
  set η := hTi.genericPoint
  have hη : closure {η} = T := hTi.isGenericPoint_genericPoint hTc
  -- The generic point `η` of `T` lies outside `U`.
  have hηU : η ∉ U := by
    intro hηU
    obtain ⟨f, hf, hfU⟩ := h η hηU
    set W := ⋃ t ∈ S.erase T, t
    have hW : IsClosed W :=
      (S.erase T).finite_toSet.isClosed_biUnion fun t ht =>
        (hS t (Finset.mem_of_mem_erase ht)).1
    obtain ⟨y, hyT, hyW⟩ := Set.not_subset.mp (hirr T hT)
    obtain ⟨z, hzT, hzD, hzW⟩ := hTi.2 (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)) Wᶜ
      (PrimeSpectrum.basicOpen f).isOpen hW.isOpen_compl
      ⟨η, hη ▸ subset_closure rfl, (PrimeSpectrum.mem_basicOpen f η).mpr hf⟩ ⟨y, hyT, hyW⟩
    have hzC : z ∈ closure Uᶜ := hCS ▸ Set.mem_iUnion₂.mpr ⟨T, hT, hzT⟩
    obtain ⟨w, ⟨hwD, hwW⟩, hwF⟩ := mem_closure_iff.mp hzC _
      ((PrimeSpectrum.basicOpen f).isOpen.inter hW.isOpen_compl) ⟨hzD, hzW⟩
    have hwT : w ∈ T := by
      obtain ⟨t, ht, hwt⟩ := Set.mem_iUnion₂.mp (hCS ▸ subset_closure hwF : w ∈ ⋃ t ∈ S, t)
      by_contra hne
      exact hwW (Set.mem_iUnion₂.mpr ⟨t, Finset.mem_erase.mpr ⟨fun e => hne (e ▸ hwt), ht⟩, hwt⟩)
    have hle : η ≤ w := by
      rw [PrimeSpectrum.le_iff_specializes, specializes_iff_mem_closure, hη]
      exact hwT
    exact hwF (hfU w hle ((PrimeSpectrum.mem_basicOpen f w).mp hwD))
  -- Hence all of `T = closure {η}` lies outside `U`.
  intro y hyT hyU
  exact hηU (hU (specializes_iff_mem_closure.mpr (hη ▸ hyT)) hyU)

end Langlands.Algebra
