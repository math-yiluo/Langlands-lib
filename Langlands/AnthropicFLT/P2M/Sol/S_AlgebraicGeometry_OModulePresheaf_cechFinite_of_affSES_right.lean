/-
Ported from `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_right.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the Apache
License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The paired Markdown file lists the changes made by the port.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Noetherian.Basic
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Langlands.AnthropicFLT.Theorems.Thm_Module_Finite_of_ker_le_range_of_isNoetherianRing
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_right

universe u
open AlgebraicGeometry _root_.AlgebraicGeometry.OModulePresheaf in
theorem solution {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
    [IsSeparated π] {F₁ F₂ F₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES F₁ F₂ F₃) (K : V.OrderedAffineCover)
    (h₁ : F₁.CechFinite K) (h₂ : F₂.CechFinite K) : F₃.CechFinite K := by
  obtain ⟨δ₀, δ, h0, hS, -, -⟩ := S.exists_connectingHom K
  refine ⟨?_, fun i => ?_⟩
  · haveI := h₂.1; haveI := h₁.2 0
    exact Module.Finite.of_ker_le_range_of_isNoetherianRing (S.proj.H0Map K) δ₀ h0
  · haveI := h₂.2 i; haveI := h₁.2 (i + 1)
    exact Module.Finite.of_ker_le_range_of_isNoetherianRing (S.proj.HSuccMap K i) (δ i) (hS i)
