import Mathlib

/-! # Generic points: maps, finiteness and prime avoidance

Generic points of irreducible components are the points without proper generalization. They
are preserved by generalizing maps and reflected by continuous maps with discrete fibres. A
finite set of points of an affine scheme inside an open subset lies in a basic open contained
in that subset (prime avoidance).
-/

universe u

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.GenericPointAvoidance

section Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

/-- In a sober `T₀` space the generic points of irreducible components are exactly the points
without proper generalization. -/
theorem mem_genericPoints_iff [T0Space α] [QuasiSober α] {x : α} :
    x ∈ genericPoints α ↔ ∀ y, y ⤳ x → y = x := by
  constructor
  · intro hx y hyx
    have hy : IsIrreducible (closure ({y} : Set α)) := isIrreducible_singleton.closure
    have hsub : closure ({x} : Set α) ⊆ closure {y} :=
      closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hyx))
        isClosed_closure
    have hle := hx.2 hy hsub
    have hxy : x ⤳ y := specializes_iff_mem_closure.mpr (hle (subset_closure rfl))
    exact (hyx.antisymm hxy).eq
  · intro hx
    refine ⟨isIrreducible_singleton.closure, fun t ht hxt => ?_⟩
    have hct : IsIrreducible (closure t) := ht.closure
    have hgen := hct.isGenericPoint_genericPoint isClosed_closure
    have hηx : hct.genericPoint ⤳ x := by
      rw [specializes_iff_mem_closure, hgen.def]
      exact subset_closure (hxt (subset_closure rfl))
    have hη := hx _ hηx
    calc t ⊆ closure t := subset_closure
      _ = closure {hct.genericPoint} := hgen.def.symm
      _ = closure {x} := by rw [hη]

/-- A generalizing map sends generic points to generic points. -/
theorem mem_genericPoints_of_generalizingMap [T0Space α] [QuasiSober α] [T0Space β]
    [QuasiSober β] {f : α → β} (hf : GeneralizingMap f) {x : α} (hx : x ∈ genericPoints α) :
    f x ∈ genericPoints β := by
  rw [mem_genericPoints_iff] at hx ⊢
  intro y hy
  obtain ⟨x', hx', rfl⟩ := hf hy
  rw [hx x' hx']

/-- A continuous map with discrete fibres reflects generic points. -/
theorem mem_genericPoints_of_isDiscrete_fibre [T0Space α] [QuasiSober α] [T0Space β]
    [QuasiSober β] {f : α → β} (hf : Continuous f) (hdisc : ∀ y, IsDiscrete (f ⁻¹' {y}))
    {x : α} (hx : f x ∈ genericPoints β) : x ∈ genericPoints α := by
  rw [mem_genericPoints_iff] at hx ⊢
  intro y hyx
  have hfy : f y = f x := hx _ (hyx.map hf)
  have hd := (hdisc (f x)).to_subtype
  have hopen : IsOpen ({⟨x, rfl⟩} : Set (f ⁻¹' {f x})) := isOpen_discrete _
  obtain ⟨O, hO, hOx⟩ := isOpen_induced_iff.mp hopen
  have hxO : x ∈ O := by
    have : (⟨x, rfl⟩ : f ⁻¹' {f x}) ∈ Subtype.val ⁻¹' O := by rw [hOx]; rfl
    exact this
  have hyO : y ∈ O := hyx.mem_open hO hxO
  have : (⟨y, hfy⟩ : f ⁻¹' {f x}) ∈ Subtype.val ⁻¹' O := hyO
  rw [hOx] at this
  exact congrArg Subtype.val this

end Topology

section PrimeAvoidance

/-- Prime avoidance: a finite set of primes disjoint from a closed set lies in a basic open
disjoint from it. -/
theorem PrimeSpectrum.exists_basicOpen_of_finite {A : Type u} [CommRing A]
    {E : Set (PrimeSpectrum A)} (hE : E.Finite) {Z : Set (PrimeSpectrum A)} (hZ : IsClosed Z)
    (hEZ : Disjoint E Z) :
    ∃ f : A, E ⊆ PrimeSpectrum.basicOpen f ∧ Disjoint (PrimeSpectrum.basicOpen f : Set _) Z := by
  classical
  let I := PrimeSpectrum.vanishingIdeal Z
  have hZI : PrimeSpectrum.zeroLocus (I : Set A) = Z := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hZ.closure_eq]
  have hnot : ∀ p ∈ E, ¬ I ≤ p.asIdeal := by
    intro p hp hIp
    have : p ∈ Z := by
      rw [← hZI]
      exact hIp
    exact Set.disjoint_left.mp hEZ hp this
  have hex : ∃ f ∈ I, ∀ p ∈ E, f ∉ p.asIdeal := by
    by_cases hEne : E.Nonempty
    · obtain ⟨p₀, -⟩ := hEne
      by_contra hcon
      push Not at hcon
      have hsub : (I : Set A) ⊆ ⋃ p ∈ (hE.toFinset : Set (PrimeSpectrum A)), (p.asIdeal : Set A) := by
        intro f hf
        obtain ⟨p, hp, hfp⟩ := hcon f hf
        exact Set.mem_biUnion (by simpa using hp) hfp
      obtain ⟨p, hp, hIp⟩ := (Ideal.subset_union_prime p₀ p₀
        (fun p _ _ _ => p.isPrime)).mp hsub
      exact hnot p (by simpa using hp) hIp
    · exact ⟨0, I.zero_mem, fun p hp => (hEne ⟨p, hp⟩).elim⟩
  obtain ⟨f, hfI, hfE⟩ := hex
  refine ⟨f, fun p hp => (PrimeSpectrum.mem_basicOpen f p).mpr (hfE p hp), ?_⟩
  rw [Set.disjoint_left]
  intro q hqf hqZ
  exact (PrimeSpectrum.mem_basicOpen f q).mp hqf
    ((PrimeSpectrum.mem_vanishingIdeal Z f).mp hfI q hqZ)

/-- Prime avoidance on an affine scheme: a finite set of points inside an open subset lies in a
basic open contained in that subset. -/
theorem exists_basicOpen_of_finite {X : Scheme.{u}} [IsAffine X] {E : Set X} (hE : E.Finite)
    {W : X.Opens} (hEW : E ⊆ W) :
    ∃ f : Γ(X, ⊤), E ⊆ X.basicOpen f ∧ X.basicOpen f ≤ W := by
  let h := X.isoSpec.hom.homeomorph
  have hdisj : Disjoint (h '' E : Set (PrimeSpectrum Γ(X, ⊤))) (h '' (W : Set X)ᶜ) := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    exact hy (h.injective hxy ▸ hEW hx)
  obtain ⟨f, hfE, hfZ⟩ := PrimeSpectrum.exists_basicOpen_of_finite (hE.image h)
    ((h.isClosed_image).mpr (W.2.isClosed_compl)) hdisj
  refine ⟨f, ?_, ?_⟩
  · intro x hx
    have : h x ∈ PrimeSpectrum.basicOpen f := hfE ⟨x, hx, rfl⟩
    rw [← Scheme.toSpecΓ_preimage_basicOpen]
    exact this
  · intro x hx
    rw [← Scheme.toSpecΓ_preimage_basicOpen] at hx
    by_contra hxW
    exact Set.disjoint_left.mp hfZ hx ⟨x, hxW, rfl⟩

end PrimeAvoidance

end Langlands.AlgebraicGeometry.GenericPointAvoidance
