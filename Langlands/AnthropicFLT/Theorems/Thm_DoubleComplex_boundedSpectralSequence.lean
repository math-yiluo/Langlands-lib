/-
Ported from `Theorems/Thm_DoubleComplex_boundedSpectralSequence.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the Apache
License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The paired Markdown file lists the changes made by the port.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_DoubleComplex
import Langlands.AnthropicFLT.P2M.Sol.S_DoubleComplex_boundedSpectralSequence
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

universe u

theorem DoubleComplex.boundedSpectralSequence : DoubleComplex.BoundedSpectralSequence.{u} := by exact @_root_.P2MW.S_DoubleComplex_boundedSpectralSequence.solution
