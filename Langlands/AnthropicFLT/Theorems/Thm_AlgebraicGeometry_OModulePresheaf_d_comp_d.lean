/-
Ported from `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the Apache
License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The paired Markdown file lists the changes made by the port.
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_d_comp_d
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


open AlgebraicGeometry

universe u
theorem AlgebraicGeometry.OModulePresheaf.d_comp_d {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (F : OModulePresheaf π) (K : V.OrderedAffineCover) (i : ℕ) : F.d K (i + 1) ∘ₗ F.d K i = 0 := by exact @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_d_comp_d.solution R _ V π F K i
