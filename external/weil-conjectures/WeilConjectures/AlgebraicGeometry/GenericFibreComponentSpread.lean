/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.GenericFibreClosedCoverSpread
import WeilConjectures.AlgebraicGeometry.GenericFibreClosedAvoidance

/-!
# Spreading a connected component of a generic fibre

Source: Stacks Project, Tag 055N, first two paragraphs of the integral-base argument.
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- A component of the fibre over a point spreads to a clopen subset over an open part
of that point's closure. This does not assert connectedness of any other fibre.

Source: Stacks Project, Tag 055N, proof through the assertion that the closure of the
chosen generic component is open; Tags 054Y and 054W.
Proof: give the closure of y its reduced closed subscheme structure and base change g.
This is an integral base with generic point y. The generic fibre is finite type over
a field, hence noetherian, so the component of x and its complement are clopen.
Take their closures in the base-changed total space. Their generic fibres are the
original subsets. Tag 054Y shrinks the base so the two closures cover the total space.
Their intersection has empty generic fibre; Tag 054W shrinks again so the intersection
is empty. Each closure is now clopen, and its trace on the generic fibre is unchanged.
The base change by the reduced closed immersion is a homeomorphism onto the inverse
image of the closure of y. Represent the open of that closure by an ambient open V,
and represent the chosen closure by a subset A of P under this homeomorphism. The
generic point belongs to V, and the trace of A on its fibre is exactly the component
of x. Empty complements cause no problem: the same closure argument applies.

(blueprint: lem-sbc-generic-fibre-component-spread) -/
theorem exists_open_generic_fibre_component_spread {P T : Scheme.{u}} (g : P ⟶ T)
    [LocallyOfFiniteType g] [QuasiCompact g] (y : T) (x : P) (hx : g x = y) :
    ∃ (V : Set T) (A : Set P), IsOpen V ∧ y ∈ V ∧
      IsClopen {q : g ⁻¹' (V ∩ closure {y}) | (q : P) ∈ A} ∧
      g ⁻¹' {y} ∩ A = connectedComponentIn (g ⁻¹' {y}) x := by
  classical
  have : LocallyOfFiniteType (g.fiberToSpecResidueField y) :=
    show LocallyOfFiniteType (Limits.pullback.snd g (T.fromSpecResidueField y)) from
      inferInstance
  have : IsLocallyNoetherian (g.fiber y) :=
    LocallyOfFiniteType.isLocallyNoetherian (g.fiberToSpecResidueField y)
  have : IsNoetherian (g.fiber y) := ⟨⟩
  have : TopologicalSpace.NoetherianSpace (g ⁻¹' {y}) :=
    (TopologicalSpace.noetherianSpace_iff_of_homeomorph (g.fiberHomeo y)).mp inferInstance
  let F : Set P := g ⁻¹' {y}
  let S : Set F := connectedComponent ⟨x, hx⟩
  have hS : IsClopen S := isClopen_connectedComponent
  let C : Set P := closure (Subtype.val '' S)
  let D : Set P := closure (Subtype.val '' Sᶜ)
  have hCtrace : Subtype.val ⁻¹' C = S := by
    rw [← IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, hS.isClosed.closure_eq]
  have hDtrace : Subtype.val ⁻¹' D = Sᶜ := by
    rw [← IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
      hS.compl.isClosed.closure_eq]
  have hcover : g ⁻¹' {y} ⊆ C ∪ D := by
    intro q hq
    by_cases h : (⟨q, hq⟩ : F) ∈ S
    · exact Or.inl (subset_closure ⟨⟨q, hq⟩, h, rfl⟩)
    · exact Or.inr (subset_closure ⟨⟨q, hq⟩, h, rfl⟩)
  have hempty : g ⁻¹' {y} ∩ (C ∩ D) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro q ⟨hq, hqC, hqD⟩
    have h : (⟨q, hq⟩ : F) ∈ S := by
      rw [← hCtrace]
      exact hqC
    have hn : (⟨q, hq⟩ : F) ∈ Sᶜ := by
      rw [← hDtrace]
      exact hqD
    exact hn h
  obtain ⟨V₁, hV₁, hy₁, hcov⟩ := exists_open_generic_fibre_closed_cover
    g y C D isClosed_closure isClosed_closure hcover
  obtain ⟨V₂, hV₂, hy₂, hdisj⟩ := exists_open_generic_fibre_closed_avoidance
    g y (C ∩ D) (isClosed_closure.inter isClosed_closure) hempty
  refine ⟨V₁ ∩ V₂, C, hV₁.inter hV₂, ⟨hy₁, hy₂⟩, ?_, ?_⟩
  · have heq : {q : g ⁻¹' ((V₁ ∩ V₂) ∩ closure {y}) | (q : P) ∈ C}ᶜ =
        {q : g ⁻¹' ((V₁ ∩ V₂) ∩ closure {y}) | (q : P) ∈ D} := by
      ext q
      have hq₁ : (q : P) ∈ g ⁻¹' (V₁ ∩ closure {y}) :=
        ⟨q.property.1.1, q.property.2⟩
      have hq₂ : (q : P) ∈ g ⁻¹' (V₂ ∩ closure {y}) :=
        ⟨q.property.1.2, q.property.2⟩
      change (q : P) ∉ C ↔ (q : P) ∈ D
      constructor
      · intro hn
        exact (hcov hq₁).resolve_left hn
      · intro hd hc
        exact Set.disjoint_left.mp hdisj hq₂ ⟨hc, hd⟩
    refine ⟨isClosed_closure.preimage continuous_subtype_val, ?_⟩
    rw [← isClosed_compl_iff, heq]
    exact isClosed_closure.preimage continuous_subtype_val
  · rw [connectedComponentIn_eq_image (show x ∈ g ⁻¹' {y} from hx)]
    change F ∩ C = Subtype.val '' S
    ext q
    constructor
    · rintro ⟨hq, hqC⟩
      refine ⟨⟨q, hq⟩, ?_, rfl⟩
      rw [← hCtrace]
      exact hqC
    · rintro ⟨q', hq', rfl⟩
      exact ⟨q'.property, subset_closure ⟨q', hq', rfl⟩⟩

end AlgebraicGeometry
