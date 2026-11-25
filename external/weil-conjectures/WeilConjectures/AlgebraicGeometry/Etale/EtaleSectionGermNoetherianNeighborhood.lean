/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Sober

/-! # A neighbourhood inside a specialization invariant locus

Source: Stacks Project, Tag 0GKC, component-shrinking paragraph.
(blueprint: lem-weil-pbc-specialization-invariant-neighborhood).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- In a sober space with finitely many irreducible components, a subset stable in
both directions under specialization contains a neighbourhood of each of its points.

Source: Stacks Project, Tag 0GKC, component-shrinking paragraph
(blueprint: lem-weil-pbc-specialization-invariant-neighborhood).

Proof: Remove the finite closed union of the components not containing the chosen
point x. The remaining open contains x. A point y in this open belongs to a component
through x. Its generic point specializes to both x and y, so stability puts y in the
subset. Empty spaces cause no difficulty since x is part of the hypotheses. -/
theorem exists_open_subset_of_specialization_invariant
    {X : Type u} [TopologicalSpace X] [QuasiSober X]
    (hfin : (irreducibleComponents X).Finite) (E : Set X)
    (hE : ∀ x y : X, x ⤳ y → (x ∈ E ↔ y ∈ E))
    (x : X) (hx : x ∈ E) :
    ∃ V : TopologicalSpace.Opens X, x ∈ V ∧ (V : Set X) ⊆ E := by
  classical
  let D := {C ∈ irreducibleComponents X | x ∉ C}
  have hD : D.Finite := hfin.subset (fun _ h ↦ h.1)
  have hc : IsClosed (⋃ C ∈ D, C) :=
    hD.isClosed_biUnion (fun C hC ↦ isClosed_of_mem_irreducibleComponents C hC.1)
  refine ⟨⟨(⋃ C ∈ D, C)ᶜ, hc.isOpen_compl⟩, ?_, ?_⟩
  · simp only [TopologicalSpace.Opens.mem_mk, Set.mem_compl_iff, Set.mem_iUnion,
      not_exists]
    exact fun C hC ↦ hC.2
  · intro y hy
    let C := irreducibleComponent y
    have hC : C ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents y
    have hyC : y ∈ C := mem_irreducibleComponent
    have hxC : x ∈ C := by
      by_contra hn
      exact hy (Set.mem_iUnion.mpr ⟨C, Set.mem_iUnion.mpr ⟨⟨hC, hn⟩, hyC⟩⟩)
    obtain ⟨η, hη⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents C hC)
    exact (hE η y (hη.specializes hyC)).mp
      ((hE η x (hη.specializes hxC)).mpr hx)

end AlgebraicGeometry.Scheme
