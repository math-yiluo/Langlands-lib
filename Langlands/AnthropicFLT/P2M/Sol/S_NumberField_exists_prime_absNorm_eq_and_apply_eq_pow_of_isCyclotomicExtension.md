# Primes of prime norm in a prescribed cyclotomic class: proof

This module proves `solution`, the statement of `NumberField.exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension`. From the divergent sum over the residue class of τ it subtracts the bounded contribution of the primes whose norm is not prime and the finitely many primes whose norm lies in S. A remaining prime v has prime norm p ∉ S with p ≡ a_τ modulo m, so τ(ζ) = ζ^p.

Source: `P2M/Sol/S_NumberField_exists_prime_absNorm_eq_and_apply_eq_pow_of_isCyclotomicExtension.lean` (entire file, 120 lines, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `f8e6f8632dcfb12e93e5803f9db0a2f96ad2d3ab76c095f2ac8e0c34cebedf55`. Declaration names and namespaces are unchanged.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the proof `Langlands.Global.chebotarevPrimeRealizationStatement` in `Langlands/Global/Arithmetic/ChebotarevPrimeRealizationProof.lean`.

Port changes: imports of FLT modules use the `Langlands.AnthropicFLT` prefix; the source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set after the imports; the audit's modification comments are replaced by the port header; the import of `P2M.Util` is dropped. Apart from the universe generalization, the mathematical hypotheses and conclusions of the source are retained.

The following edits of the audit `notes/reuse/anthropic-chebotarev-audit.md` are applied. Its evidence files `compatibility.md`, `universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact diffs.

- Universes: `universe u v w` is declared; the binder of `K` (originally `Type`) is `Type u`; the binder of `L` (originally `Type`) is `Type v`. The audit named these universes `audit_u`, `audit_v`, `audit_w`.
- Cleanup: the line `attribute [-instance] Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G` was removed.
