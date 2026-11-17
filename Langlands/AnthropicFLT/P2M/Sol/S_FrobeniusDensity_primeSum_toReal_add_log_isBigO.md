# The prime sum differs from −log(s − 1) by a bounded amount: proof

This module proves `solution`, the statement of `FrobeniusDensity.primeSum_toReal_add_log_isBigO`. It proves finite Euler products for the sums over ideals supported on a finite set of primes, and exhausts all ideals by finite sets of prime factors. This places log of the ideal sum between the prime sum and the prime sum plus a constant coming from Σ_v N(v)^(−2). The pole of the ideal sum at 1 then gives the estimate.

Source: `P2M/Sol/S_FrobeniusDensity_primeSum_toReal_add_log_isBigO.lean` (entire file, 474 lines, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `920441c4e0e84499f6cef5513421a53ee1cbdc84564e01ea72419a4de4b15ebd`. Declaration names and namespaces are unchanged.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the proof `Langlands.Global.chebotarevPrimeRealizationStatement` in `Langlands/Global/Arithmetic/ChebotarevPrimeRealizationProof.lean`.

Port changes: imports of FLT modules use the `Langlands.AnthropicFLT` prefix; the source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set after the imports; the audit's modification comments are replaced by the port header; the import of `P2M.Util` is dropped and its commands are replaced by ordinary Lean commands: 3 `p2m_open` commands by `open _root_.…`, 2 `p2m_export` commands by `export _root_.… (…)`. Apart from the universe generalization, the mathematical hypotheses and conclusions of the source are retained.

The following edits of the audit `notes/reuse/anthropic-chebotarev-audit.md` are applied. Its evidence files `compatibility.md`, `universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact diffs.

- Compatibility with Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435` (the source pins Lean 4.33.1 and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`): in `one_le_idealSum` and `one_le_factoredSum`, the summand of `ENNReal.le_tsum` is now given explicitly as `(f := fun I => normRpow K s I.1)` on the subtype of summation.
- Universes: `universe u v w` is declared; the binder of `K` (originally `Type*`) is `Type u`. The audit named these universes `audit_u`, `audit_v`, `audit_w`.
