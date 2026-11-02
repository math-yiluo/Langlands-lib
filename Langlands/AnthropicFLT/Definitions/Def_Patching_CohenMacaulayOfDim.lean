/-
Ported from `Definitions/Def_Patching_CohenMacaulayOfDim.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports. The paired Markdown file lists
the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_Patching_SystemTypes
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace IsLocalRing

variable (R : Type*) [CommRing R] [IsLocalRing R]

def IsCohenMacaulayOfDim (d : ℕ) : Prop :=
  ringKrullDim R = d ∧ Module.depth R R = d

namespace IsCohenMacaulayOfDim

variable {R} {d : ℕ}

lemma ringKrullDim_eq (h : IsCohenMacaulayOfDim R d) : ringKrullDim R = d := h.1

lemma depth_eq (h : IsCohenMacaulayOfDim R d) : Module.depth R R = d := h.2

end IsCohenMacaulayOfDim

end IsLocalRing
