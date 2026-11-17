# Bound for the primes of higher residue degree: proof

This module proves `solution`, the statement of `FrobeniusDensity.tailSum_le`. A prime v whose absolute norm is not a prime number has norm p^f with f ≥ 2, where p is the rational prime below v. Hence N(v)^(−s) ≤ p^(−2) for s ≥ 1, and at most [K : ℚ] primes lie above each p. Summing over the fibres above the rational primes gives the bound.

Source: `P2M/Sol/S_FrobeniusDensity_tailSum_le.lean` (entire file, 158 lines, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `b7ff5345e56748111f0aa5e34e4491c9a731013204f0cf2957ce4e6cfdfe9f6e`. Declaration names and namespaces are unchanged.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the proof `Langlands.Global.chebotarevPrimeRealizationStatement` in `Langlands/Global/Arithmetic/ChebotarevPrimeRealizationProof.lean`.

Port changes: imports of FLT modules use the `Langlands.AnthropicFLT` prefix; the source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set after the imports; the audit's modification comments are replaced by the port header; the import of `P2M.Util` is dropped and its commands are replaced by ordinary Lean commands: 2 `p2m_open` commands by `open _root_.…`, 2 `p2m_reactivate` commands by `open scoped _root_.…`, 1 `p2m_export` command by `export _root_.… (…)`. Apart from the universe generalization, the mathematical hypotheses and conclusions of the source are retained.

The following edits of the audit `notes/reuse/anthropic-chebotarev-audit.md` are applied. Its evidence files `compatibility.md`, `universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact diffs.

- Universes: `universe u v w` is declared; the binder of `K` (originally `Type*`) is `Type u`. The audit named these universes `audit_u`, `audit_v`, `audit_w`.
