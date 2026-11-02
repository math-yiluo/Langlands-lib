/-
Ported from `P2M/Sol/S_AlgebraicGeometry_Scheme_existsUnique_hom_sigma_of_disjoint_iSup_eq_top.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; universe levels are generalized. The paired Markdown file lists
the changes.
-/
import Mathlib
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace P2MW.S_AlgebraicGeometry_Scheme_existsUnique_hom_sigma_of_disjoint_iSup_eq_top

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem solution
    {σ : Type*} [Small.{u} σ] (H : σ → Scheme.{u}) {T : Scheme.{u}} (U : σ → T.Opens)
    (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j)) (hcov : (⨆ i, U i) = ⊤)
    (v : ∀ i, ((U i : T.Opens) : Scheme.{u}) ⟶ H i) :
    ∃! u : T ⟶ ∐ H, ∀ i, (U i).ι ≫ u = v i ≫ Sigma.ι H i := by
  let 𝒰 : T.OpenCover := T.openCoverOfIsOpenCover U (IsOpenCover.mk hcov)
  have hcompat : ∀ i j : σ, pullback.fst (𝒰.f i) (𝒰.f j) ≫ (v i ≫ Sigma.ι H i) =
      pullback.snd (𝒰.f i) (𝒰.f j) ≫ (v j ≫ Sigma.ι H j) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [fst_eq_snd_of_mono_eq]
    ·
      haveI : IsEmpty ↥(pullback (𝒰.f i) (𝒰.f j)) := by
        refine ⟨fun x => ?_⟩
        have hx : (pullback.fst (𝒰.f i) (𝒰.f j)).base x ∈ Set.range (pullback.fst (𝒰.f i) (𝒰.f j)).base := ⟨x, rfl⟩
        rw [Scheme.Pullback.range_fst] at hx
        obtain ⟨y, hy⟩ := hx
        have h1 : ((𝒰.f i).base ((pullback.fst (𝒰.f i) (𝒰.f j)).base x)) ∈ (U i : Set T) := by
          simp only [Scheme.openCoverOfIsOpenCover_f, 𝒰]
          exact Subtype.property _
        have h2 : ((𝒰.f j).base y) ∈ (U j : Set T) := by
          simp only [Scheme.openCoverOfIsOpenCover_f, 𝒰]
          exact Subtype.property _
        rw [hy] at h2
        exact Set.disjoint_iff.mp (Opens.coe_disjoint.mpr (hdisj i j hij)) ⟨h1, h2⟩
      exact (isInitialOfIsEmpty).hom_ext _ _
  refine ⟨Scheme.Cover.glueMorphisms 𝒰 (fun i => v i ≫ Sigma.ι H i) hcompat, fun i => ?_, fun u' hu' => ?_⟩
  · exact Scheme.Cover.ι_glueMorphisms 𝒰 _ hcompat i
  · refine Scheme.Cover.hom_ext 𝒰 _ _ fun i => ?_
    rw [Scheme.Cover.ι_glueMorphisms 𝒰 _ hcompat i]
    exact hu' i
