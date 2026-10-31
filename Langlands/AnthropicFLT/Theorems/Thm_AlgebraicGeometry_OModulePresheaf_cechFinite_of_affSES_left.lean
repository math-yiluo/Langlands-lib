/-
Ported from `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_left.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the Apache
License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The paired Markdown file lists the changes made by the port.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Noetherian.Basic
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_left
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


open AlgebraicGeometry

universe u
theorem AlgebraicGeometry.OModulePresheaf.cechFinite_of_affSES_left {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsSeparated π] {F₁ F₂ F₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES F₁ F₂ F₃) (K : V.OrderedAffineCover) (h₂ : F₂.CechFinite K) (h₃ : F₃.CechFinite K) : F₁.CechFinite K := by exact @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_left.solution R _ _ V π _ F₁ F₂ F₃ S K h₂ h₃
