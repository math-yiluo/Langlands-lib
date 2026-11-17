# The pole of the ideal Dirichlet series at 1

`FrobeniusDensity.tendsto_sub_one_mul_idealSum_test`: for a number field K, (s − 1) times the real value of Σ_{I ≠ 0} N(I)^(−s) tends to Mathlib's Dedekind zeta residue `dedekindZeta_residue K` as s → 1⁺. The proof applies the solution module.

Source: `Theorems/Thm_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean` (entire file, 10 lines) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `5404bf91344aebf49164caae0d33ffc21fc9de443f7ec87ca3333fc817f69365`. Declaration names and namespaces are unchanged.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the proof `Langlands.Global.chebotarevPrimeRealizationStatement` in `Langlands/Global/Arithmetic/ChebotarevPrimeRealizationProof.lean`.

Port changes: imports of FLT modules use the `Langlands.AnthropicFLT` prefix; the source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set after the imports; the audit's modification comments are replaced by the port header; the import of `P2M.Util` is dropped. Apart from the universe generalization, the mathematical hypotheses and conclusions of the source are retained.

The following edits of the audit `notes/reuse/anthropic-chebotarev-audit.md` are applied. Its evidence files `compatibility.md`, `universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact diffs.

- Universes: `universe u v w` is declared; the binder of `K` (originally `Type*`) is `Type u`. The audit named these universes `audit_u`, `audit_v`, `audit_w`.
- Cleanup: the proof `by p2m_exact_reverting @_root_.P2MW.S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.solution` was replaced by `apply @_root_.P2MW.S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.solution <;> assumption`.
