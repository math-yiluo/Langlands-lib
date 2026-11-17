# Divergence of the prime sums in each cyclotomic residue class: proof

This module proves `solution`, the statement of `NumberField.exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension`, in 846 source lines. It expresses the indicator of the residue class through Dirichlet characters modulo m pulled back to the narrow ray class group by the norm. The splitting theorem gives a lower bound for the sum over primes of K of norm 1 modulo m, which it compares with the prime sums of L.

For each nontrivial pulled-back character, the L-series does not vanish at 1. The argument is by contradiction: a zero would occur for every character in a fibre of the pullback, whose size is at least the annihilator, and would cancel the logarithmic pole of the principal part against the positive lower bound. This bounds the logarithms of the nonprincipal L-series near 1. Comparing cardinalities identifies the image of the norm character with the cyclotomic Galois image. The sum over the residue class of τ is then unbounded as s → 1⁺.

Source: `P2M/Sol/S_NumberField_exists_forall_le_tsum_absNorm_rpow_neg_of_isCyclotomicExtension.lean` (entire file, 846 lines, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `b24bfe92818b4582c66d7190ab673487b87fece45e4af265bfca9515b61d6da9`. Declaration names and namespaces are unchanged.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the proof `Langlands.Global.chebotarevPrimeRealizationStatement` in `Langlands/Global/Arithmetic/ChebotarevPrimeRealizationProof.lean`.

Port changes: imports of FLT modules use the `Langlands.AnthropicFLT` prefix; the source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set after the imports; the audit's modification comments are replaced by the port header; the import of `P2M.Util` is dropped. Apart from the universe generalization, the mathematical hypotheses and conclusions of the source are retained.

The following edits of the audit `notes/reuse/anthropic-chebotarev-audit.md` are applied. Its evidence files `compatibility.md`, `universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact diffs.

- Universes: `universe u v w` is declared; the binder of `K` (originally `Type`) is `Type u`; the binder of `L` (originally `Type`) is `Type v`; the binder of `F` (originally `Type`) is `Type*`. The audit named these universes `audit_u`, `audit_v`, `audit_w`.
