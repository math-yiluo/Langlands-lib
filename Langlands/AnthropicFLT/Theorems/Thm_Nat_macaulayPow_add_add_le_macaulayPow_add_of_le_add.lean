/-
Ported from `Theorems/Thm_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.Definitions.Def_Nat_MacaulayPow
import Langlands.AnthropicFLT.P2M.Sol.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Nat.macaulayPow_add_add_le_macaulayPow_add_of_le_add
    (d x y u v : ℕ) (hd : 1 ≤ d) (hx : x ≤ u + v)
    (hu : Nat.macaulayPow d u + y ≤ Nat.macaulayPow d y)
    (hv : Nat.macaulayPow (d + 1) v + x ≤ Nat.macaulayPow (d + 1) x) :
    Nat.macaulayPow (d + 1) x + (x + y) ≤ Nat.macaulayPow (d + 1) (x + y) :=
  P2MW.S_Nat_macaulayPow_add_add_le_macaulayPow_add_of_le_add.solution d x y u v hd hx hu hv
