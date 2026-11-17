# The absolute-norm character of a narrow ray class group

Let K be a number field and q a natural number. For a height-one prime v, `normClass K q v` is the class of N(v) in (ℤ/q)ˣ if N(v) is coprime to q, and 1 otherwise. The module proves the following.
- If α is a nonzero algebraic integer with α ≡ 1 modulo q, then N_{K/ℚ}(α) ≡ 1 modulo q.
- If α is moreover totally positive, then N_{K/ℚ}(α) > 0.
- The ray symbol of `normClass` is the norm class of every nonzero ideal.

Hence, when (q) divides 𝔣, the ray symbol of `normClass` kills the narrow ray subgroup. It therefore descends to a character `normClassChar` from the narrow ray class group modulo 𝔣 to (ℤ/q)ˣ, which sends the class of a prime to its norm class.

Source: `Definitions/Def_LanglandsTunnell_NormClass.lean` (entire file, 291 lines) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `5082eecb75998923c27eb04cf5e7be564403f19233efe4217596372e8c224938`. Declaration names and namespaces are unchanged.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the proof `Langlands.Global.chebotarevPrimeRealizationStatement` in `Langlands/Global/Arithmetic/ChebotarevPrimeRealizationProof.lean`.

Port changes: imports of FLT modules use the `Langlands.AnthropicFLT` prefix; the source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set after the imports; the audit's modification comments are replaced by the port header. Apart from the universe generalization, the mathematical hypotheses and conclusions of the source are retained.

The following edits of the audit `notes/reuse/anthropic-chebotarev-audit.md` are applied. Its evidence files `compatibility.md`, `universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact diffs.

- Universes: `universe u v w` is declared; the binder of `K` (originally `Type*`) is `Type u`. The audit named these universes `audit_u`, `audit_v`, `audit_w`.
