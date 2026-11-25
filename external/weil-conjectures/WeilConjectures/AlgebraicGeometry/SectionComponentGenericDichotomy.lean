/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.AlgebraicGeometry.SectionComponentGenericClopen

/-!
# Generic dichotomy for the component selected by a section

Source: Stacks Project, Tag 055P, noetherian argument, using Tag 055N.
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- On a nonempty open part of any irreducible closed subset, the section component is
uniformly present or uniformly absent.

Source: Stacks Project, Tag 055P, final paragraph, using Tags 055N and 055M.
Proof: let x be the generic point of Z and y = g(x). Give the closure of y its reduced
closed subscheme structure and base change g and its section to it. Tag 055M identifies
its section component with the inverse image of the original component. Over this
integral base the generic fibre is noetherian, and its section component is clopen and
geometrically connected because it has a rational section point. Take the closures of
this component and its complement in the total space. After shrinking the base about
y, these closures cover the total space and are disjoint (055N, using 054Y and 054W).
After a further shrinking, geometric connectedness of the first closure's fibres
persists (055G). Shrink also so that the section lands in the first closure. Thus the
section component is clopen over a nonempty open V of the closure of y. The trace
W = Z intersect g inverse image V is a nonempty open of Z, containing x; it is
irreducible. The component's trace on W is clopen, hence empty or all of W. Express W
as Z intersect an ambient open U, giving the asserted alternatives. No constructibility
criterion is used in this step.

(blueprint: lem-sbc-section-component-generic-dichotomy) -/
theorem exists_open_section_component_dichotomy {P T : Scheme.{u}}
    [IsNoetherian P] [IsNoetherian T] (g : P ⟶ T)
    [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g]
    (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T) (Z : Set P)
    (hZ : IsClosed Z) (hZi : IsIrreducible Z) :
    ∃ U : Set P, IsOpen U ∧ (U ∩ Z).Nonempty ∧
      (U ∩ Z ⊆ {q : P | q ∈ connectedComponentIn (g ⁻¹' {g q}) (σ (g q))} ∨
       U ∩ Z ⊆ {q : P | q ∈ connectedComponentIn (g ⁻¹' {g q}) (σ (g q))}ᶜ) := by
  classical
  obtain ⟨x, hx⟩ := QuasiSober.sober hZi hZ
  obtain ⟨V, hV, hxV, hC⟩ := exists_open_section_component_clopen g σ hσ (g x)
  let U : Set P := g ⁻¹' V
  have hU : IsOpen U := hV.preimage g.continuous
  have hUZ : (U ∩ Z).Nonempty := ⟨x, hxV, hx.mem⟩
  have hW : IsPreirreducible (U ∩ Z) := by
    intro A B hA hB hWA hWB
    obtain ⟨a, haW, haA⟩ := hWA
    obtain ⟨b, hbW, hbB⟩ := hWB
    obtain ⟨q, hqZ, hqUA, hqUB⟩ := hZi.isPreirreducible (U ∩ A) (U ∩ B)
      (hU.inter hA) (hU.inter hB) ⟨a, haW.2, haW.1, haA⟩
      ⟨b, hbW.2, hbW.1, hbB⟩
    exact ⟨q, ⟨hqUA.1, hqZ⟩, hqUA.2, hqUB.2⟩
  let : PreirreducibleSpace ↥(U ∩ Z) := Subtype.preirreducibleSpace hW
  have himage : ∀ q ∈ Z, g q ∈ closure {g x} := by
    intro q hq
    exact specializes_iff_mem_closure.mp ((hx.specializes hq).map g.continuous)
  let i : ↥(U ∩ Z) → g ⁻¹' (V ∩ closure {g x}) :=
    fun q => ⟨q.1, q.2.1, himage q.1 q.2.2⟩
  have hi : Continuous i := continuous_subtype_val.subtype_mk _
  let C : Set ↥(g ⁻¹' (V ∩ closure {g x})) :=
    {q | (q : P) ∈ connectedComponentIn (g ⁻¹' {g (q : P)}) (σ (g (q : P)))}
  have hCW : IsClopen (i ⁻¹' C) := hC.preimage hi
  refine ⟨U, hU, hUZ, ?_⟩
  rcases isClopen_iff.mp hCW with hempty | hall
  · right
    intro q hq hqC
    have hmem : (⟨q, hq⟩ : ↥(U ∩ Z)) ∈ i ⁻¹' C := hqC
    rw [hempty] at hmem
    exact hmem
  · left
    intro q hq
    have hmem : (⟨q, hq⟩ : ↥(U ∩ Z)) ∈ i ⁻¹' C := by
      rw [hall]
      exact Set.mem_univ _
    exact hmem

end AlgebraicGeometry
