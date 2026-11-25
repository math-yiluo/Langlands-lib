/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Topology.NoetherianSpace

/-!
# Dense affine open subschemes of noetherian schemes

A scheme whose underlying space is noetherian has a dense affine open subscheme
(`AlgebraicGeometry.Scheme.exists_isAffineOpen_dense`): the disjoint union of affine opens, one in
each irreducible component and avoiding the other components.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A scheme whose underlying space is noetherian has a dense affine open subscheme: the
disjoint union of affine opens, one in each irreducible component and avoiding the others. -/
theorem Scheme.exists_isAffineOpen_dense (X : Scheme.{u}) [NoetherianSpace X] :
    ∃ V : X.Opens, IsAffineOpen V ∧ Dense (V : Set X) := by
  classical
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents
  let O : irreducibleComponents X → Set X := fun Z ↦ (⋃₀ (irreducibleComponents X \ {Z.1}))ᶜ
  have hOopen : ∀ Z, IsOpen (O Z) := fun Z ↦ by
    dsimp only [O]
    rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact hfin.sdiff.isClosed_biUnion fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
  have hOcl : ∀ Z, closure (O Z) = Z := fun Z ↦
    closure_sUnion_irreducibleComponents_sdiff_singleton hfin Z.1 Z.2
  have hOne : ∀ Z, (O Z).Nonempty := fun Z ↦ by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have := hOcl Z
    rw [h, closure_empty] at this
    exact Z.2.1.nonempty.ne_empty this.symm
  have hOsub : ∀ Z, O Z ⊆ Z := fun Z ↦ (hOcl Z) ▸ subset_closure
  have hOdisj : ∀ Z Z' : irreducibleComponents X, Z ≠ Z' → Disjoint (O Z) (Z' : Set X) := by
    intro Z Z' h
    refine Set.disjoint_left.2 fun x hx hx' ↦ hx ⟨Z', ⟨Z'.2, fun e ↦ h (Subtype.ext e.symm)⟩, hx'⟩
  choose x hx using hOne
  have hV : ∀ Z, ∃ V : X.Opens, IsAffineOpen V ∧ x Z ∈ V ∧ (V : Set X) ⊆ O Z := fun Z ↦ by
    obtain ⟨V, hV, hxV, hVO⟩ :=
      exists_isAffineOpen_mem_and_subset (U := ⟨O Z, hOopen Z⟩) (hx Z)
    exact ⟨V, hV, hxV, hVO⟩
  choose V hVaff hxV hVO using hV
  have : Finite (irreducibleComponents X) := hfin.to_subtype
  refine ⟨⨆ Z, V Z, IsAffineOpen.iSup_of_disjoint hVaff fun Z Z' h ↦ ?_, ?_⟩
  · rw [Function.onFun, ← Opens.coe_disjoint]
    exact ((hOdisj Z Z' h).mono_left (hVO Z)).mono_right ((hVO Z').trans (hOsub Z'))
  · rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro y
    obtain ⟨Z, hZ, hyZ⟩ := Set.mem_sUnion.1 ((sUnion_irreducibleComponents (X := X)).symm ▸
      Set.mem_univ y)
    have h₁ : (Z : Set X) ⊆ closure (Z ∩ V ⟨Z, hZ⟩) :=
      subset_closure_inter_of_isPreirreducible_of_isOpen hZ.1.2 (V ⟨Z, hZ⟩).isOpen
        ⟨x ⟨Z, hZ⟩, hOsub ⟨Z, hZ⟩ (hx ⟨Z, hZ⟩), hxV _⟩
    refine closure_mono ?_ (h₁ hyZ)
    exact Set.inter_subset_right.trans (SetLike.coe_subset_coe.2 (le_iSup V ⟨Z, hZ⟩))

end AlgebraicGeometry
