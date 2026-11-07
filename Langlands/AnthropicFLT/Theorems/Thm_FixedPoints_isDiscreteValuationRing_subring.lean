/-
Ported from `Theorems/Thm_FixedPoints_isDiscreteValuationRing_subring.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; `p2m_exact_reverting` is replaced by `exact` with explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_FixedPoints_isDiscreteValuationRing_subring
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype

set_option autoImplicit false

theorem FixedPoints.isDiscreteValuationRing_subring
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {H : Type*} [Group H] [Finite H] [MulSemiringAction H R] :
    IsDiscreteValuationRing (FixedPoints.subring R H) := by exact @_root_.P2MW.S_FixedPoints_isDiscreteValuationRing_subring.solution R _ _ _ H _ _ _
