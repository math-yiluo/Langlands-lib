/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Irreducible

@[expose] public section

universe u v

open Topology

namespace AlgebraicGeometry

/-- If finitely many upstairs components descend to closed subsets under a continuous
surjection, inverse images of downstairs components are upstairs components.

Source: the maximality argument following finite descent in Stacks Project, Tag 054R;
the finite closed-cover criterion is Mathlib's `isIrreducible_iff_sUnion_isClosed`.
Proof: the images of upstairs components form a finite closed cover downstairs. Each image
is irreducible by continuity. An irreducible component downstairs lies in one member of
this cover, and maximality makes them equal. Its inverse image is the upstairs component,
since each upstairs component is the inverse image of a downstairs subset and the map is
surjective. Empty spaces cause no exception, since there are then no downstairs components.
(blueprint: new-lem-sbc-closed-component-descent-topology) -/
theorem component_preimages_of_closed_descent {Y : Type u} {Z : Type v}
    [TopologicalSpace Y] [TopologicalSpace Z] (p : Y → Z)
    (hp : Continuous p) (hsurj : Function.Surjective p)
    (hfinite : (irreducibleComponents Y).Finite)
    (hdesc : ∀ C ∈ irreducibleComponents Y, ∃ A : Set Z, IsClosed A ∧ p ⁻¹' A = C) :
    ∀ A ∈ irreducibleComponents Z, p ⁻¹' A ∈ irreducibleComponents Y := by
  classical
  let S : Set (Set Z) := Set.image (Set.image p) (irreducibleComponents Y)
  have hS : S.Finite := hfinite.image (Set.image p)
  have hclosed : ∀ A ∈ S, IsClosed A := by
    rintro _ ⟨C, hC, rfl⟩
    obtain ⟨A, hA, heq⟩ := hdesc C hC
    rw [← heq, Set.image_preimage_eq _ hsurj]
    exact hA
  have hcover : (Set.univ : Set Z) ⊆ ⋃₀ S := by
    intro z _
    obtain ⟨y, rfl⟩ := hsurj z
    exact Set.mem_sUnion.mpr ⟨p '' irreducibleComponent y,
      ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y, rfl⟩,
      Set.mem_image_of_mem p mem_irreducibleComponent⟩
  intro A hA
  obtain ⟨B, hB, hAB⟩ := isIrreducible_iff_sUnion_isClosed.mp hA.1 hS.toFinset
    (fun B hB ↦ hclosed B (hS.mem_toFinset.mp hB))
    (hS.coe_toFinset.symm ▸ (Set.subset_univ A).trans hcover)
  obtain ⟨C, hC, rfl⟩ := hS.mem_toFinset.mp hB
  have heq : p '' C = A := Set.Subset.antisymm
    (hA.2 (hC.1.image p hp.continuousOn) hAB) hAB
  obtain ⟨D, _, hD⟩ := hdesc C hC
  rw [← heq, ← hD, Set.image_preimage_eq _ hsurj]
  rwa [hD]

end AlgebraicGeometry
