# Every automorphism of a Galois extension of number fields is a Frobenius: proof

This module proves `solution`, the statement of `NumberField.exists_prime_isArithFrobAt_of_isGalois`, by reduction to the cyclotomic case (435 source lines). Let n be the order of σ and D = [L : ℚ]. The proof runs as follows.
1. Choose a prime q ≡ 1 modulo n·D!. Let L′ = L(ζ_q) be the q-th cyclotomic field over L; it is Galois over K and lives in universe `w`.
2. The kernel N of the restriction map Gal(L′/K) → Gal(L/K) embeds into (ℤ/q)ˣ by the cyclotomic character, and n divides #N.
3. Lift σ to σ₁ ∈ Gal(L′/K). A lemma on cyclic groups gives h ∈ N such that #N divides the order of the cyclotomic character of σ′ = σ₁h. Then σ′ still restricts to σ, and a power of σ′ fixes ζ_q only if it is 1.
4. Hence L′ is cyclotomic for {q} over the fixed field M of ⟨σ′⟩. `NumberField.exists_prime_isArithFrobAt_of_isCyclotomicExtension`, applied over M to σ′, gives a prime p ∉ S and a maximal P′ of the ring of integers of L′ at which σ′ is an arithmetic Frobenius.
5. The contraction P of P′ to the ring of integers of L is maximal and contains p, and the Frobenius congruence of σ′ restricts to that of σ at P.

The proof does not use the theorem it proves.

Source: `P2M/Sol/S_NumberField_exists_prime_isArithFrobAt_of_isGalois.lean` (entire file, 435 lines, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `79beb303a6260626e3fce4278aedff9b1fa94ef1e79aba7d49cc82d9be590305`. Declaration names and namespaces are unchanged.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the proof `Langlands.Global.chebotarevPrimeRealizationStatement` in `Langlands/Global/Arithmetic/ChebotarevPrimeRealizationProof.lean`.

Port changes: imports of FLT modules use the `Langlands.AnthropicFLT` prefix; the source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set after the imports; the audit's modification comments are replaced by the port header; the import of `P2M.Util` is dropped and its commands are replaced by ordinary Lean commands: 2 `p2m_reactivate` commands by `open scoped _root_.…`. Apart from the universe generalization, the mathematical hypotheses and conclusions of the source are retained.

The following edits of the audit `notes/reuse/anthropic-chebotarev-audit.md` are applied. Its evidence files `compatibility.md`, `universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact diffs.

- Universes: `universe u v w` is declared; the binder of `K` (originally `Type`) is `Type u`; the binder of `L` (originally `Type`) is `Type v`; the binder of `L'` (originally `Type`) is `Type w`. The audit named these universes `audit_u`, `audit_v`, `audit_w`.
- Cleanup: the line `attribute [-instance] FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G` was removed; the line `attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec` was removed.
