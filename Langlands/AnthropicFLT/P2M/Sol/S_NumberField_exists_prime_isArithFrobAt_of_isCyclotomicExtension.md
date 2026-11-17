# Realization of automorphisms of cyclotomic extensions as Frobenius elements: proof

This module proves `solution`, the statement of `NumberField.exists_prime_isArithFrobAt_of_isCyclotomicExtension`. The previous theorem gives v of prime norm p ∉ S with τ(ζ) = ζ^p, and p is coprime to m. Take a maximal ideal Q of the ring of integers of L over v. Mathlib's Frobenius of Q relative to the ring of integers of K sends ζ to ζ^p. An automorphism is determined by its value on ζ, so this Frobenius is τ. Since ℤ/(Q ∩ ℤ) and the residue field of v both have p elements, the relative Frobenius congruence is the absolute one over ℤ.

Source: `P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension.lean` (entire file, 146 lines, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `9ea7b5917696dac67dc8c33c6551b1bbf3c4122f49d9bc1b8fe9bf272ab6dab6`. Declaration names and namespaces are unchanged.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the proof `Langlands.Global.chebotarevPrimeRealizationStatement` in `Langlands/Global/Arithmetic/ChebotarevPrimeRealizationProof.lean`.

Port changes: imports of FLT modules use the `Langlands.AnthropicFLT` prefix; the source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set after the imports; the audit's modification comments are replaced by the port header; the import of `P2M.Util` is dropped. Apart from the universe generalization, the mathematical hypotheses and conclusions of the source are retained.

The following edits of the audit `notes/reuse/anthropic-chebotarev-audit.md` are applied. Its evidence files `compatibility.md`, `universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact diffs.

- Universes: `universe u v w` is declared; the binder of `K` (originally `Type`) is `Type u`; the binder of `L` (originally `Type`) is `Type v`. The audit named these universes `audit_u`, `audit_v`, `audit_w`.
- Cleanup: the line `attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G` was removed; the line `attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec` was removed.
