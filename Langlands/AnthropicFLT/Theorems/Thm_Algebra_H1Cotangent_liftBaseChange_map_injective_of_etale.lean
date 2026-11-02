/-
Ported from `Theorems/Thm_Algebra_H1Cotangent_liftBaseChange_map_injective_of_etale.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_etale
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct

theorem Algebra.H1Cotangent.liftBaseChange_map_injective_of_etale (R D T : Type u)
    [CommRing R] [CommRing D] [CommRing T] [Algebra R D] [Algebra D T] [Algebra R T] [IsScalarTower R D T]
    [Algebra.Etale D T] :
    Function.Injective ((Algebra.H1Cotangent.map R R D T).liftBaseChange T) :=
  P2MW.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_etale.solution R D T
