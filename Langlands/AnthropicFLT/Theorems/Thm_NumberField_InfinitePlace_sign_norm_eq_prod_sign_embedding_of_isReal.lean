/-
Ported from `Theorems/Thm_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.lean`
(entire file, 14 lines) of the Anthropic Lean formalization of Fermat's Last Theorem: registered
source `anthropic-flt-complete-lean-source-6e837e75`, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, original file SHA256
d68c0266d95147742f1729f5ea70c0b0f91452668c7bd49ec3c5faee2a3c9121.
Copyright 2026 Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.

Complete list of edits to the source text (the paired Markdown file gives the same list; the audit
`notes/reuse/anthropic-chebotarev-audit.md` and its evidence files `compatibility.md`,
`universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact
diffs):
- Imports of FLT modules use the `Langlands.AnthropicFLT` prefix.
- The source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set
  after the imports.
- The audit's modification comments are replaced by the port header.
- The import of `P2M.Util` is dropped.
- Universes: `universe u v w` is declared; the binder of `K` (originally `Type`) is `Type u`. The
  audit named these universes `audit_u`, `audit_v`, `audit_w`.
- Cleanup: the proof `by p2m_exact_reverting
  @_root_.P2MW.S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.solution` was
  replaced by `apply
  @_root_.P2MW.S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.solution <;>
  assumption`.

Declaration names and namespaces are unchanged. Apart from the universe generalization, the
mathematical hypotheses and conclusions of the source are retained.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

set_option autoImplicit false

open NumberField NumberField.InfinitePlace

open scoped Classical in

theorem NumberField.InfinitePlace.sign_norm_eq_prod_sign_embedding_of_isReal
    (K : Type u) [Field K] [NumberField K] {x : K} (hx : x ≠ 0) :
    SignType.sign (Algebra.norm ℚ x) =
      ∏ w : {w : InfinitePlace K // w.IsReal}, SignType.sign (embedding_of_isReal w.2 x) := by
  apply @_root_.P2MW.S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.solution <;> assumption
