/-
Ported from `Definitions/Def_Nat_MacaulayPow.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports. The paired Markdown file lists
the changes.
-/
import Mathlib
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Nat

def macaulayPow : ℕ → ℕ → ℕ
  | 0, _ => 0
  | d + 1, a =>
      (Nat.findGreatest (fun k => k.choose (d + 1) ≤ a) (a + d + 1) + 1).choose (d + 2) +
        macaulayPow d (a - (Nat.findGreatest (fun k => k.choose (d + 1) ≤ a) (a + d + 1)).choose (d + 1))

end Nat
