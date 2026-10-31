/-
Ported from `Theorems/Thm_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the Apache
License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The paired Markdown file lists the changes made by the port.
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Properties
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


open AlgebraicGeometry TopologicalSpace

universe u
theorem AlgebraicGeometry.Scheme.isIntegral_subscheme_vanishingIdeal {V : Scheme.{u}} (Z : Closeds V) (hZ : IsIrreducible (Z : Set V)) : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal.solution V Z hZ
