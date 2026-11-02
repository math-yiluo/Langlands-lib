/-
Ported from `Theorems/Thm_ProjSpaceCech_GradedModule_subsingleton_cohomology_shift_of_isFG.lean` of the Anthropic Lean formalization of
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
import Langlands.AnthropicFLT.P2M.Sol.S_ProjSpaceCech_GradedModule_subsingleton_cohomology_shift_of_isFG
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ProjSpaceCech.GradedModule.subsingleton_cohomology_shift_of_isFG {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (M : ProjSpaceCech.GradedModule R n) (hM : ProjSpaceCech.GradedModule.IsFG M) :
    ∃ d₀ : ℤ, ∀ d, d₀ ≤ d → ∀ i, 1 ≤ i → Subsingleton (ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.shift M d) i) :=
  P2MW.S_ProjSpaceCech_GradedModule_subsingleton_cohomology_shift_of_isFG.solution M hM
