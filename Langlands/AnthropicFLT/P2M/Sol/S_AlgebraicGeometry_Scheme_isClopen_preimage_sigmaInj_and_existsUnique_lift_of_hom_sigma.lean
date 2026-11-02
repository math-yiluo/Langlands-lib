/-
Ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped and its commands are replaced
by standard Lean commands; universe levels are generalized. The paired Markdown file lists the changes.
-/
import Mathlib
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace P2MW.S_AlgebraicGeometry_Scheme_isClopen_preimage_sigmaInj_and_existsUnique_lift_of_hom_sigma

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace CoprodPtsA

variable {σ : Type*} [Small.{u} σ] (H : σ → Scheme.{u}) {T : Scheme.{u}} (u : T ⟶ ∐ H)

theorem isClosed_opensRange (i : σ) : IsClosed ((Sigma.ι H i).opensRange : Set ↥(∐ H)) := by
  classical
  have hcov : (⨆ j, (Sigma.ι H j).opensRange) = ⊤ := by
    have h := (sigmaOpenCover H).iSup_opensRange
    simp only [sigmaOpenCover_f] at h
    exact h
  have hcompl : ((Sigma.ι H i).opensRange : Set ↥(∐ H))ᶜ =
      ⋃ j ∈ ({i}ᶜ : Set σ), ((Sigma.ι H j).opensRange : Set ↥(∐ H)) := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_compl_singleton_iff, exists_prop]
    constructor
    · intro hx
      have hx' : x ∈ ((⨆ j, (Sigma.ι H j).opensRange : (∐ H).Opens) : Set ↥(∐ H)) := by
        rw [hcov]; trivial
      rw [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion] at hx'
      obtain ⟨j, hj⟩ := hx'
      exact ⟨j, fun h => hx (h ▸ hj), hj⟩
    · rintro ⟨j, hji, hj⟩ hx
      exact Set.disjoint_iff.mp (Opens.coe_disjoint.mpr
        (disjoint_opensRange_sigmaι H i j (Ne.symm hji))) ⟨hx, hj⟩
  rw [← isOpen_compl_iff, hcompl]
  exact isOpen_biUnion fun j _ => (Sigma.ι H j).opensRange.isOpen

private theorem _root_.CoprodPtsA.iSup_opensRange : (⨆ i, (Sigma.ι H i).opensRange) = ⊤ := by
  have h := (sigmaOpenCover H).iSup_opensRange
  simp only [sigmaOpenCover_f] at h
  exact h

theorem closed (i : σ) : IsClosed ((u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Set T) :=
  (isClosed_opensRange H i).preimage u.continuous

theorem disjoint (i j : σ) (hij : i ≠ j) :
    Disjoint (u ⁻¹ᵁ (Sigma.ι H i).opensRange) (u ⁻¹ᵁ (Sigma.ι H j).opensRange) :=
  Opens.coe_disjoint.mp ((Opens.coe_disjoint.mpr (disjoint_opensRange_sigmaι H i j hij)).preimage u.base)

theorem cover : (⨆ i, u ⁻¹ᵁ (Sigma.ι H i).opensRange) = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, _root_.CoprodPtsA.iSup_opensRange, Scheme.Hom.preimage_top]

theorem range_subset (i : σ) :
    Set.range ((u ⁻¹ᵁ (Sigma.ι H i).opensRange).ι ≫ u).base ⊆ Set.range (Sigma.ι H i).base := by
  rintro _ ⟨x, rfl⟩
  have hx : (x.1 : T) ∈ (u ⁻¹ᵁ (Sigma.ι H i).opensRange : Set T) := x.2
  have hx' : u.base x.1 ∈ Set.range (Sigma.ι H i).base := by
    rw [← Scheme.Hom.coe_opensRange]; exact hx
  simpa using hx'

private theorem _root_.CoprodPtsA.lift (i : σ) : ∃! v : ((u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Scheme.{u}) ⟶ H i,
      v ≫ Sigma.ι H i = (u ⁻¹ᵁ (Sigma.ι H i).opensRange).ι ≫ u := by
  refine ⟨IsOpenImmersion.lift (Sigma.ι H i) _ (range_subset H u i), IsOpenImmersion.lift_fac _ _ _, fun v hv => ?_⟩
  rw [← cancel_mono (Sigma.ι H i), hv, IsOpenImmersion.lift_fac]

theorem finite [CompactSpace T] :
    {i : σ | ((u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Set T).Nonempty}.Finite := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i => ((u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Set T)) (fun i => (u ⁻¹ᵁ _).isOpen)
    (by
      intro x _
      have hx : x ∈ ((⨆ i, u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Set T) := by rw [cover]; trivial
      simpa [Opens.coe_iSup] using hx)
  refine t.finite_toSet.subset ?_
  rintro j ⟨x, hx⟩
  obtain ⟨i, hi, hxi⟩ : ∃ i ∈ t, x ∈ ((u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Set T) := by
    simpa using ht (Set.mem_univ x)
  by_cases hij : i = j
  · exact hij ▸ hi
  · exact ((Set.disjoint_iff.mp (Opens.coe_disjoint.mpr (disjoint H u i j hij))) ⟨hxi, hx⟩).elim

end CoprodPtsA

theorem solution
    {σ : Type*} [Small.{u} σ] (H : σ → Scheme.{u}) {T : Scheme.{u}} (u : T ⟶ ∐ H) :
    (∀ i, IsClosed ((u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Set T)) ∧
    (∀ i j, i ≠ j → Disjoint (u ⁻¹ᵁ (Sigma.ι H i).opensRange) (u ⁻¹ᵁ (Sigma.ι H j).opensRange)) ∧
    (⨆ i, u ⁻¹ᵁ (Sigma.ι H i).opensRange) = ⊤ ∧
    (∀ i, ∃! v : ((u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Scheme.{u}) ⟶ H i,
      v ≫ Sigma.ι H i = (u ⁻¹ᵁ (Sigma.ι H i).opensRange).ι ≫ u) ∧
    (CompactSpace T → {i : σ | ((u ⁻¹ᵁ (Sigma.ι H i).opensRange : T.Opens) : Set T).Nonempty}.Finite) :=
  ⟨CoprodPtsA.closed H u, CoprodPtsA.disjoint H u, CoprodPtsA.cover H u, CoprodPtsA.lift H u,
    fun _ => CoprodPtsA.finite H u⟩
