/-
Ported from `Theorems/Thm_ProjSpaceCech_GradedModule_Presentation_subsingleton_H_of_ses.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import Langlands.AnthropicFLT.P2M.Sol.S_ProjSpaceCech_GradedModule_Presentation_subsingleton_H_of_ses
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.Presentation.subsingleton_H_of_ses {R : Type u} [CommRing R] {n : ℕ} {D : ProjSpaceCech.GradedModule R n}
    (σ : ProjSpaceCech.GradedModule.Presentation D) (i : ℕ)
    (hF : Subsingleton (ProjSpaceCech.GradedModule.H σ.F i)) (hK : Subsingleton (ProjSpaceCech.GradedModule.H σ.ker (i + 1))) :
    Subsingleton (ProjSpaceCech.GradedModule.H D i) :=
  P2MW.S_ProjSpaceCech_GradedModule_Presentation_subsingleton_H_of_ses.solution σ i hF hK
