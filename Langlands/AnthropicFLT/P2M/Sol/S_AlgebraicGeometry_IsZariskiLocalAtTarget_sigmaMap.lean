/-
Ported from `P2M/Sol/S_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap.lean` of the Anthropic Lean formalization of
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
namespace P2MW.S_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap

set_option autoImplicit false
universe u
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (sigmaMk_mk Scheme.Hom IsZariskiLocalAtTarget Scheme sigmaι_eq_iff IsOpenImmersion sigmaOpenCover IsZariskiLocalAtTarget.of_openCover sigmaMk IsOpenImmersion.isPullback Scheme.Hom.comp_apply)
namespace SigmaMapU4
open _root_.AlgebraicGeometry

variable {σ : Type*} [Small.{u} σ] {X Y : σ → Scheme.{u}} (f : ∀ i, X i ⟶ Y i)

theorem sigmaMap_sigmaι_apply (i : σ) (x : X i) :
    (Limits.Sigma.map f) ((Limits.Sigma.ι X i) x) = (Limits.Sigma.ι Y i) (f i x) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Limits.Sigma.ι_map]

set_option backward.isDefEq.respectTransparency false in

theorem isPullback_sigmaι_sigmaMap (j : σ) :
    IsPullback (f j) (Limits.Sigma.ι X j) (Limits.Sigma.ι Y j) (Limits.Sigma.map f) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (by simp) ?_
  apply le_antisymm
  · rintro x ⟨y, hxy⟩
    obtain ⟨i, x, rfl⟩ : ∃ i, ∃ x' : X i, (Limits.Sigma.ι X i) x' = x := by
      have hcov : (⨆ i, (Limits.Sigma.ι X i).opensRange) = ⊤ := by
        have h := (sigmaOpenCover X).iSup_opensRange
        simp only [sigmaOpenCover_f] at h
        exact h
      have hx : x ∈ ((⨆ i, (Limits.Sigma.ι X i).opensRange : (∐ X).Opens) : Set ↥(∐ X)) := by
        rw [hcov]; trivial
      rw [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion] at hx
      obtain ⟨i, hi⟩ := hx
      rw [Scheme.Hom.coe_opensRange] at hi
      obtain ⟨x', hx'⟩ := hi
      exact ⟨i, x', hx'⟩
    have hxy' : (Limits.Sigma.ι Y j) y = (Limits.Sigma.ι Y i) (f i x) := by
      rw [← sigmaMap_sigmaι_apply]; exact hxy
    obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp ((sigmaι_eq_iff Y j i _ _).mp hxy')
    exact ⟨x, rfl⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨f j x, (sigmaMap_sigmaι_apply f j x).symm⟩

end AlgebraicGeometry.SigmaMapU4

open AlgebraicGeometry.SigmaMapU4 in
set_option backward.isDefEq.respectTransparency false in
theorem solution
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    {σ : Type*} [Small.{u} σ] {X Y : σ → Scheme.{u}} (f : ∀ i, X i ⟶ Y i) (hf : ∀ i, P (f i)) :
    P (Limits.Sigma.map f) := by
  refine IsZariskiLocalAtTarget.of_openCover (sigmaOpenCover Y) ?_
  intro j
  show P (Limits.pullback.snd (Limits.Sigma.map f) (Limits.Sigma.ι Y j))
  rw [← MorphismProperty.cancel_left_of_respectsIso P (isPullback_sigmaι_sigmaMap f j).flip.isoPullback.hom,
    IsPullback.isoPullback_hom_snd]
  exact hf j
