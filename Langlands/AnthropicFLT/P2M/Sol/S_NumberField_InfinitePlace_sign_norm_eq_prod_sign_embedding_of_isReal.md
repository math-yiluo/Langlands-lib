# Sign of the norm as a product over real places: proof

This module proves `solution`, the statement of `NumberField.InfinitePlace.sign_norm_eq_prod_sign_embedding_of_isReal`. It writes N_{K/ℚ}(x) as the product of the images of x under all complex embeddings. The non-real embeddings come in conjugate pairs, each contributing a positive factor |τ(x)|². The sign is therefore the product of the signs at the real places.

Source: `P2M/Sol/S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.lean` (entire file, 94 lines, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `d5fe13c2a44f1e7c5f01d23b2b7dfc9a9ab222876d90de43f0949ac08a8861c2`. Declaration names and namespaces are unchanged.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the proof `Langlands.Global.chebotarevPrimeRealizationStatement` in `Langlands/Global/Arithmetic/ChebotarevPrimeRealizationProof.lean`.

Port changes: imports of FLT modules use the `Langlands.AnthropicFLT` prefix; the source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set after the imports; the audit's modification comments are replaced by the port header; the import of `P2M.Util` is dropped. Apart from the universe generalization, the mathematical hypotheses and conclusions of the source are retained.

The following edits of the audit `notes/reuse/anthropic-chebotarev-audit.md` are applied. Its evidence files `compatibility.md`, `universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact diffs.

- Universes: `universe u v w` is declared; the binder of `K` (originally `Type`) is `Type u`. The audit named these universes `audit_u`, `audit_v`, `audit_w`.
