/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

import WeilConjectures.Mathlib.Topology.Constructible
import WeilConjectures.AlgebraicGeometry.SectionComponentNoetherianModel
import WeilConjectures.AlgebraicGeometry.SectionComponentGenericDichotomy

/-!
# Local constructibility of the component selected by a section

Source: Stacks Project, Tag 055P.
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- The relative connected component of a section is locally constructible.

Source: Stacks Project, Tag 055P, with base-change compatibility from Tag 055M.
Proof: work over an affine open of the base. Finite presentation descends the morphism
and section to a finite type Z-algebra. The component of a rational section point is
geometrically connected, so the locus commutes with base change. On the noetherian model,
consider any irreducible closed subset Z of the source, with generic point x and image y.
Tag 055N supplies a nonempty open V in the closure of y on which the section component
is clopen. Put W = Z intersected with the inverse image of V, a nonempty open of Z.
Since W is irreducible, its intersection with the component locus is empty or all of W.
Thus the locus in Z is not dense or contains a nonempty open. The noetherian
constructibility criterion proves constructibility. Pulling back proves local
constructibility. Quasi-compactness and quasi-separatedness make local finite
presentation into finite presentation, as required for this descent.

(blueprint: lem-sbc-section-component-locally-constructible) -/
theorem isLocallyConstructible_section_component {P T : Scheme.{u}} (g : P ⟶ T)
    [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g]
    (σ : T ⟶ P) (hσ : σ ≫ g = 𝟙 T) :
    IsLocallyConstructible {p : P | p ∈ connectedComponentIn (g ⁻¹' {g p}) (σ (g p))} := by
  have hnoeth {P₀ T₀ : Scheme.{u}} [IsNoetherian P₀] [IsNoetherian T₀]
      (g₀ : P₀ ⟶ T₀) [LocallyOfFinitePresentation g₀] [QuasiCompact g₀]
      [QuasiSeparated g₀] (σ₀ : T₀ ⟶ P₀) (hσ₀ : σ₀ ≫ g₀ = 𝟙 T₀) :
      IsConstructible
        {q : P₀ | q ∈ connectedComponentIn (g₀ ⁻¹' {g₀ q}) (σ₀ (g₀ q))} := by
    let C := {q : P₀ | q ∈ connectedComponentIn (g₀ ⁻¹' {g₀ q}) (σ₀ (g₀ q))}
    have H (Z : TopologicalSpace.Closeds P₀) : IsConstructible (C ∩ (Z : Set P₀)) := by
      apply wellFounded_lt.induction Z
      clear Z
      intro Z ih
      by_cases hZe : Z = ⊥
      · simp [hZe]
      by_cases hZi : IsPreirreducible (Z : Set P₀)
      · obtain ⟨U, hU, hUZ, hCU⟩ := exists_open_section_component_dichotomy
          g₀ σ₀ hσ₀ Z Z.isClosed ⟨TopologicalSpace.Closeds.coe_nonempty.mpr hZe, hZi⟩
        let W : TopologicalSpace.Closeds P₀ :=
          ⟨(Z : Set P₀) ∩ Uᶜ, Z.isClosed.inter hU.isClosed_compl⟩
        have hW : W < Z := by
          refine lt_of_le_of_ne Set.inter_subset_left ?_
          intro heq
          obtain ⟨x, hxU, hxZ⟩ := hUZ
          have hxW : x ∈ W := heq.symm ▸ hxZ
          exact hxW.2 hxU
        have hCW := ih W hW
        rcases hCU with hCU | hCU
        · have heq : C ∩ (Z : Set P₀) = (C ∩ (W : Set P₀)) ∪ (U ∩ Z) := by
            ext x
            change (x ∈ C ∧ x ∈ Z) ↔
              ((x ∈ C ∧ x ∈ Z ∧ x ∉ U) ∨ (x ∈ U ∧ x ∈ Z))
            have hx := fun hxU hxZ ↦ hCU (show x ∈ U ∩ Z from ⟨hxU, hxZ⟩)
            tauto
          rw [heq]
          exact hCW.union (hU.isConstructible_of_noetherianSpace.inter
            Z.isClosed.isConstructible_of_noetherianSpace)
        · have heq : C ∩ (Z : Set P₀) = C ∩ (W : Set P₀) := by
            ext x
            change (x ∈ C ∧ x ∈ Z) ↔ (x ∈ C ∧ x ∈ Z ∧ x ∉ U)
            have hx := fun hxU hxZ ↦ hCU (show x ∈ U ∩ Z from ⟨hxU, hxZ⟩)
            tauto
          rwa [heq]
      · simp only [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at hZi
        obtain ⟨Z₁, Z₂, hZ₁, hZ₂, hcover, h₁, h₂⟩ := hZi
        let W₁ : TopologicalSpace.Closeds P₀ := ⟨Z₁, hZ₁⟩
        let W₂ : TopologicalSpace.Closeds P₀ := ⟨Z₂, hZ₂⟩
        have hW₁ : Z ⊓ W₁ < Z := inf_lt_left.mpr h₁
        have H₁ := ih (Z ⊓ W₁) hW₁
        have hW₂ : Z ⊓ W₂ < Z := inf_lt_left.mpr h₂
        have H₂ := ih (Z ⊓ W₂) hW₂
        have heq : C ∩ (Z : Set P₀) =
            (C ∩ ((Z ⊓ W₁ : TopologicalSpace.Closeds P₀) : Set P₀)) ∪
            (C ∩ ((Z ⊓ W₂ : TopologicalSpace.Closeds P₀) : Set P₀)) := by
          ext x
          have hx : x ∈ Z → (x ∈ Z₁ ∨ x ∈ Z₂) := fun hxZ ↦ hcover hxZ
          change (x ∈ C ∧ x ∈ Z) ↔
            ((x ∈ C ∧ x ∈ Z ∧ x ∈ Z₁) ∨ (x ∈ C ∧ x ∈ Z ∧ x ∈ Z₂))
          tauto
        rw [heq]
        exact H₁.union H₂
    simpa [C] using H ⊤
  intro p
  obtain ⟨U, hpU, P₀, T₀, g₀, σ₀, ρ, hP₀, hT₀, hg₀, hqc₀, hqs₀, hσ₀, heq⟩ :=
    exists_section_component_noetherian_model g σ hσ p
  let := hP₀
  let := hT₀
  let := hg₀
  let := hqc₀
  let := hqs₀
  refine ⟨U, U.isOpen.mem_nhds hpU, U.isOpen, ?_⟩
  change IsConstructible (U.ι ⁻¹'
    {q : P | q ∈ connectedComponentIn (g ⁻¹' {g q}) (σ (g q))})
  rw [heq]
  exact ρ.isConstructible_preimage (hnoeth g₀ σ₀ hσ₀)

end AlgebraicGeometry
