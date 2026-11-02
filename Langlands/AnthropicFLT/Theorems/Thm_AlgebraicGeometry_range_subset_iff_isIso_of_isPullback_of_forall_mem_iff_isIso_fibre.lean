/-
Ported from `Theorems/Thm_AlgebraicGeometry_range_subset_iff_isIso_of_isPullback_of_forall_mem_iff_isIso_fibre.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_range_subset_iff_isIso_of_isPullback_of_forall_mem_iff_isIso_fibre
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.range_subset_iff_isIso_of_isPullback_of_forall_mem_iff_isIso_fibre
    {𝒳 Y 𝒵 : Scheme.{u}} (p : 𝒵 ⟶ Y) (q : 𝒳 ⟶ Y) (h : 𝒵 ⟶ 𝒳) (w : h ≫ q = p)
    (U : Y.Opens)
    (hU : ∀ y : Y, y ∈ (U : Set Y) ↔
      IsIso (pullback.map p (Y.fromSpecResidueField y) q (Y.fromSpecResidueField y) h (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp])))
    (hUiso : IsIso (pullback.map p U.ι q U.ι h (𝟙 _) (𝟙 _) (by rw [Category.comp_id, w])
      (by rw [Category.comp_id, Category.id_comp])))
    {T Z X' : Scheme.{u}} (t : T ⟶ Y)
    (pZ : Z ⟶ T) (eZ : Z ⟶ 𝒵) (hZ : IsPullback eZ pZ p t)
    (qX : X' ⟶ T) (eX : X' ⟶ 𝒳) (hX : IsPullback eX qX q t)
    (φ : Z ⟶ X') (hφ₁ : φ ≫ qX = pZ) (hφ₂ : φ ≫ eX = eZ ≫ h) :
    Set.range t.base ⊆ (U : Set Y) ↔ IsIso φ :=
  P2MW.S_AlgebraicGeometry_range_subset_iff_isIso_of_isPullback_of_forall_mem_iff_isIso_fibre.solution p q h w U hU hUiso t pZ eZ hZ qX eX hX φ hφ₁ hφ₂
