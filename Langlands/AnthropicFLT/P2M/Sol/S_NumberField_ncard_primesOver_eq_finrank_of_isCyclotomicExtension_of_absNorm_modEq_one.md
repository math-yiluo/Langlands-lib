# Complete splitting of primes of norm 1 modulo m in cyclotomic extensions: proof

This module proves `solution`, the statement of `NumberField.ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one`.

Reduction of m-th roots of unity is injective modulo a prime not dividing m, so the inertia groups above v are trivial. The Frobenius at a prime w above v sends ζ to ζ^(N v). Since N(v) ≡ 1 modulo m, it fixes ζ and is therefore the identity. Every residue class then satisfies y^q = y with q = N(v), so the residue field of w has N(v) elements. The degree formula Σ e·f = [L : K] gives [L : K] primes, each of norm N(v).

Source: `P2M/Sol/S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean` (entire file, 233 lines, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `92270468e21b711b4876a47527d03c77810457ef74ae195b4da9e4014996af30`. Declaration names and namespaces are unchanged.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the proof `Langlands.Global.chebotarevPrimeRealizationStatement` in `Langlands/Global/Arithmetic/ChebotarevPrimeRealizationProof.lean`.

Port changes: imports of FLT modules use the `Langlands.AnthropicFLT` prefix; the source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set after the imports; the audit's modification comments are replaced by the port header; the import of `P2M.Util` is dropped. Apart from the universe generalization, the mathematical hypotheses and conclusions of the source are retained.

The following edits of the audit `notes/reuse/anthropic-chebotarev-audit.md` are applied. Its evidence files `compatibility.md`, `universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact diffs.

- Compatibility with Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435` (the source pins Lean 4.33.1 and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`): in `main`, two steps `simp [hζ'def, hζ.coe_toInteger] at h` became `change (σ : L ≃ₐ[K] L) ζ = ζ at h` and `change φ ζ = ζ at h`.
- Universes: `universe u v w` is declared; the binder of `K` (originally `Type`) is `Type u`; the binder of `L` (originally `Type`) is `Type v`. The audit named these universes `audit_u`, `audit_v`, `audit_w`.
