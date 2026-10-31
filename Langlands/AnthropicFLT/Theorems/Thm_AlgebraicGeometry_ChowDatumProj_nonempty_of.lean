/-
Ported from `Theorems/Thm_AlgebraicGeometry_ChowDatumProj_nonempty_of.lean` of the Anthropic Lean formalization of Fermat's Last Theorem
(commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026 Anthropic, PBC, licensed under the Apache
License, Version 2.0; see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
The paired Markdown file lists the changes made by the port.
-/
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ChowDatumProj_nonempty_of
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
theorem AlgebraicGeometry.ChowDatumProj.nonempty_of {R : Type u} [CommRing R] {V : Scheme.{u}}
    (π : V ⟶ Spec (.of R)) : Nonempty (ChowDatum π) → Nonempty (ChowDatumProj π) := by exact @_root_.P2MW.S_AlgebraicGeometry_ChowDatumProj_nonempty_of.solution R _ V π
