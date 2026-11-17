# The pole of the ideal Dirichlet series at 1: proof

This module proves `solution`, the statement of `FrobeniusDensity.tendsto_sub_one_mul_idealSum_test`. It groups the ideals by norm, identifies the real sum with the Dedekind zeta function at real s > 1, and applies Mathlib's residue theorem `dedekindZeta_residue`.

Source: `P2M/Sol/S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.lean` (entire file, 148 lines, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `a214f39af2e6dc8624d80634a5203007c9574aa86ec565779187e210b60fab76`. Declaration names and namespaces are unchanged.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the proof `Langlands.Global.chebotarevPrimeRealizationStatement` in `Langlands/Global/Arithmetic/ChebotarevPrimeRealizationProof.lean`.

Port changes: imports of FLT modules use the `Langlands.AnthropicFLT` prefix; the source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set after the imports; the audit's modification comments are replaced by the port header; the import of `P2M.Util` is dropped and its commands are replaced by ordinary Lean commands: 3 `p2m_open` commands by `open _root_.…`, 1 `p2m_export` command by `export _root_.… (…)`. Apart from the universe generalization, the mathematical hypotheses and conclusions of the source are retained.

The following edits of the audit `notes/reuse/anthropic-chebotarev-audit.md` are applied. Its evidence files `compatibility.md`, `universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact diffs.

- Universes: `universe u v w` is declared; the binder of `K` (originally `Type*`) is `Type u`. The audit named these universes `audit_u`, `audit_v`, `audit_w`.
