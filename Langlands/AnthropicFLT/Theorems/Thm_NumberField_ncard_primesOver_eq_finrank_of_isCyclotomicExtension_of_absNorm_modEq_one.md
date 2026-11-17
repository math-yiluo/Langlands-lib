# Complete splitting of primes of norm 1 modulo m in cyclotomic extensions

`NumberField.ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one`: let L/K be an extension of number fields that is cyclotomic for {m}, and v a maximal ideal of the ring of integers of K with N(v) coprime to m and N(v) ≡ 1 modulo m. Then v has exactly [L : K] primes above it in the ring of integers of L, and each has absolute norm N(v). The proof applies the solution module.

Source: `Theorems/Thm_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean` (entire file, 16 lines) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `e69890e27cae1f08c39b27c271ca570d143cb61016c14a47f3d7fede2bb404bd`. Declaration names and namespaces are unchanged.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the proof `Langlands.Global.chebotarevPrimeRealizationStatement` in `Langlands/Global/Arithmetic/ChebotarevPrimeRealizationProof.lean`.

Port changes: imports of FLT modules use the `Langlands.AnthropicFLT` prefix; the source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set after the imports; the audit's modification comments are replaced by the port header; the import of `P2M.Util` is dropped. Apart from the universe generalization, the mathematical hypotheses and conclusions of the source are retained.

The following edits of the audit `notes/reuse/anthropic-chebotarev-audit.md` are applied. Its evidence files `compatibility.md`, `universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact diffs.

- Universes: `universe u v w` is declared; the binder of `K` (originally `Type`) is `Type u`; the binder of `L` (originally `Type`) is `Type v`. The audit named these universes `audit_u`, `audit_v`, `audit_w`.
- Cleanup: the line `attribute [-instance] Deep.NTSupply.instNormalRayClassSubgroup` was removed; the proof `by p2m_exact_reverting @_root_.P2MW.S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.solution` was replaced by `apply @_root_.P2MW.S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.solution (m := m) <;> assumption`, where the modulus m is passed explicitly.
