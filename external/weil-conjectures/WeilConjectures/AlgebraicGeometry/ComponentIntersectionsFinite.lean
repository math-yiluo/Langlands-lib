/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Component intersections on a Noetherian scheme of dimension at most one

Source: Stacks Project, Varieties, Lemma 33.38.10 (Tag 09NX), proof, first paragraph
and the uniqueness assertion in its final paragraph
(blueprint: lem-sc-component-intersections-finite).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- On a Noetherian scheme of topological dimension at most one, the irreducible components
are finite in number, their distinct pairwise intersections are finite sets of closed points,
and outside their union each point belongs to exactly one component.
Source: Stacks Project, Varieties, Lemma 33.38.10 (Tag 09NX), proof
(blueprint: lem-sc-component-intersections-finite).

Proof: The Noetherian hypothesis gives finitely many components. For distinct components,
maximality shows that the first is not contained in the second, so the complement of the
second in the first is a nonempty open. The first component is irreducible, sober, Noetherian
and of dimension at most one. The source library's
`IsOpen.finite_compl_of_topologicalKrullDim_le_one` makes its complement finite, and
`IsOpen.isClosed_singleton_of_mem_compl` makes its points closed in the component. The closed
embedding into the scheme preserves these closed singletons. Taking the finite union over
distinct component pairs gives the finite closed-point set T. Every point belongs to
`irreducibleComponent y`; outside T any other component containing it must equal this one. -/
theorem component_intersections_finite (Y : Scheme.{u}) [IsLocallyNoetherian Y]
    [CompactSpace Y] (h_dim : topologicalKrullDim Y ≤ 1) :
    let T : Set Y := {y | ∃ Z₁ ∈ irreducibleComponents Y,
      ∃ Z₂ ∈ irreducibleComponents Y, Z₁ ≠ Z₂ ∧ y ∈ Z₁ ∩ Z₂}
    (irreducibleComponents Y).Finite ∧
    (∀ Z₁ ∈ irreducibleComponents Y, ∀ Z₂ ∈ irreducibleComponents Y, Z₁ ≠ Z₂ →
      (Z₁ ∩ Z₂).Finite ∧ ∀ y ∈ Z₁ ∩ Z₂, IsClosed ({y} : Set Y)) ∧
    T.Finite ∧ (∀ y ∈ T, IsClosed ({y} : Set Y)) ∧
    ∀ y : Y, y ∉ T → ∃! Z : Set Y, Z ∈ irreducibleComponents Y ∧ y ∈ Z := by
  classical
  let : IsNoetherian Y := ⟨⟩
  dsimp only
  let T : Set Y := {y | ∃ Z₁ ∈ irreducibleComponents Y,
    ∃ Z₂ ∈ irreducibleComponents Y, Z₁ ≠ Z₂ ∧ y ∈ Z₁ ∩ Z₂}
  have hcomponents : (irreducibleComponents Y).Finite :=
    finite_irreducibleComponents_of_isNoetherian
  have hpairs : ∀ Z₁ ∈ irreducibleComponents Y, ∀ Z₂ ∈ irreducibleComponents Y,
      Z₁ ≠ Z₂ → (Z₁ ∩ Z₂).Finite ∧ ∀ y ∈ Z₁ ∩ Z₂, IsClosed ({y} : Set Y) := by
    intro Z₁ hZ₁ Z₂ hZ₂ hne
    have hc₁ := isClosed_of_mem_irreducibleComponents Z₁ hZ₁
    have hc₂ := isClosed_of_mem_irreducibleComponents Z₂ hZ₂
    let : IrreducibleSpace Z₁ := Subtype.irreducibleSpace hZ₁.1
    let : QuasiSober Z₁ := hc₁.isClosedEmbedding_subtypeVal.quasiSober
    have hd : topologicalKrullDim Z₁ ≤ 1 :=
      Topology.IsInducing.subtypeVal.topologicalKrullDim_le.trans h_dim
    let U : Set Z₁ := Subtype.val ⁻¹' Z₂ᶜ
    have hU : IsOpen U := hc₂.isOpen_compl.preimage continuous_subtype_val
    have hUne : U.Nonempty := by
      by_contra hempty
      have hsub : Z₁ ⊆ Z₂ := by
        intro y hy
        by_contra hy₂
        exact hempty ⟨⟨y, hy⟩, hy₂⟩
      exact hne (hsub.antisymm (hZ₁.2 hZ₂.1 hsub))
    constructor
    · refine ((hU.finite_compl_of_topologicalKrullDim_le_one hd hUne).image
        (Subtype.val : Z₁ → Y)).subset ?_
      intro y hy
      exact ⟨⟨y, hy.1⟩, fun h ↦ h hy.2, rfl⟩
    · intro y hy
      have hcy : IsClosed ({⟨y, hy.1⟩} : Set Z₁) :=
        hU.isClosed_singleton_of_mem_compl hd hUne (fun h ↦ h hy.2)
      simpa using hc₁.isClosedMap_subtype_val _ hcy
  have hTfinite : T.Finite := by
    have hbig : (⋃ Z₁ ∈ irreducibleComponents Y, ⋃ Z₂ ∈ irreducibleComponents Y,
        ⋃ (_ : Z₁ ≠ Z₂), Z₁ ∩ Z₂).Finite :=
      hcomponents.biUnion fun Z₁ hZ₁ ↦ hcomponents.biUnion fun Z₂ hZ₂ ↦
        Set.finite_iUnion fun hne ↦ (hpairs Z₁ hZ₁ Z₂ hZ₂ hne).1
    refine hbig.subset ?_
    intro y hy
    obtain ⟨Z₁, hZ₁, Z₂, hZ₂, hne, hy⟩ := hy
    exact Set.mem_iUnion.2 ⟨Z₁, Set.mem_iUnion.2 ⟨hZ₁,
      Set.mem_iUnion.2 ⟨Z₂, Set.mem_iUnion.2 ⟨hZ₂, Set.mem_iUnion.2 ⟨hne, hy⟩⟩⟩⟩⟩
  refine ⟨hcomponents, hpairs, hTfinite, ?_, ?_⟩
  · intro y hy
    obtain ⟨Z₁, hZ₁, Z₂, hZ₂, hne, hy⟩ := hy
    exact (hpairs Z₁ hZ₁ Z₂ hZ₂ hne).2 y hy
  · intro y hy
    refine ⟨irreducibleComponent y,
      ⟨irreducibleComponent_mem_irreducibleComponents y, mem_irreducibleComponent⟩, ?_⟩
    intro Z hZ
    by_contra hne
    exact hy ⟨Z, hZ.1, irreducibleComponent y,
      irreducibleComponent_mem_irreducibleComponents y, hne,
      hZ.2, mem_irreducibleComponent⟩

end AlgebraicGeometry
