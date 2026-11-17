# Counting primes of residue degree one

For a number field K and a natural number ℓ, `FrobeniusDensity.degOneCount K ℓ` is the number of primes of the ring of integers of K lying over ℓℤ whose residue ring has exactly ℓ elements when ℓ is prime, and 0 otherwise.

For a Galois number field L, the Prop-valued definition `FrobeniusDensity.DegOneAsymptotic L` says the following. For every subgroup H of Gal(L/ℚ) and every finite set S₀ of naturals, let F be the fixed field of H. Then the series Σ_{ℓ ∉ S₀} degOneCount(F, ℓ) ℓ^(−s) converges for real s > 1, and its sum plus log(s − 1) is O(1) as s → 1⁺. This is a definition only: the port neither proves nor assumes it.

Source: `Definitions/Def_FrobeniusDensity_DegOneAsymptotic.lean` (entire file, 44 lines) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `3fa91cc61916676dd0c95fc1a691282e1437d24b71ca03b2bdd4e28c78ab3ef7`. Declaration names and namespaces are unchanged.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the proof `Langlands.Global.chebotarevPrimeRealizationStatement` in `Langlands/Global/Arithmetic/ChebotarevPrimeRealizationProof.lean`.

Port changes: imports of FLT modules use the `Langlands.AnthropicFLT` prefix; the source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set after the imports; the audit's modification comments are replaced by the port header. Apart from the universe generalization, the mathematical hypotheses and conclusions of the source are retained.

The following edits of the audit `notes/reuse/anthropic-chebotarev-audit.md` are applied. Its evidence files `compatibility.md`, `universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact diffs.

- Universes: `universe u v w` is declared; the binder of `K` (originally `Type*`) is `Type u`; the binder of `L` (originally `Type*`) is `Type v`. The audit named these universes `audit_u`, `audit_v`, `audit_w`.
