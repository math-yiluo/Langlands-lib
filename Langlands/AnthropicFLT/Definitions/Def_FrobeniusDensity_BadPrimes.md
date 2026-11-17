# Ramified rational primes and conjugacy of Frobenius elements

Let L be a number field. The module proves that ℤ/ℓℤ has ℓ elements, and that ℤ/(Q ∩ ℤ) has ℓ elements when an ideal Q of the ring of integers of L lies over ℓℤ. Over a number field K it proves that only finitely many height-one primes divide a nonzero ideal.

For a Galois number field L it proves the following.
- A nontrivial automorphism moves some algebraic integer.
- Only finitely many height-one primes have nontrivial inertia group.
- Define `badPrimes L` as the finite set of naturals made of 0, 1 and the rational primes below the primes with nontrivial inertia. For a prime ℓ outside `badPrimes L`, every prime of the ring of integers of L lying over ℓℤ has trivial inertia group.
- The arithmetic Frobenius elements at two primes over the same rational prime ℓ are conjugate.
- `realizesCyclicAt_of_exists`: to prove `RealizesCyclicAt L σ ℓ`, it suffices to find one prime over ℓ whose Frobenius is conjugate to a power of σ coprime to the order of σ.

It also gives the values of `degOneCount` at prime and at nonprime ℓ.

Source: `Definitions/Def_FrobeniusDensity_BadPrimes.lean` (entire file, 126 lines) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `5c757222b2715ab2b31b337d7a07d29ff5fe349a41e3138d2d5c99f515415f96`. Declaration names and namespaces are unchanged.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the proof `Langlands.Global.chebotarevPrimeRealizationStatement` in `Langlands/Global/Arithmetic/ChebotarevPrimeRealizationProof.lean`.

Port changes: imports of FLT modules use the `Langlands.AnthropicFLT` prefix; the source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set after the imports; the audit's modification comments are replaced by the port header. Apart from the universe generalization, the mathematical hypotheses and conclusions of the source are retained.

The following edits of the audit `notes/reuse/anthropic-chebotarev-audit.md` are applied. Its evidence files `compatibility.md`, `universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact diffs.

- Compatibility with Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435` (the source pins Lean 4.33.1 and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`): in `finite_setOf_dvd`, the step `simpa [Multiset.mem_toFinset] using …` became `exact Multiset.mem_toFinset.mpr (…)` with the same term.
- Universes: `universe u v w` is declared; the binder of `K` (originally `Type*`) is `Type u`; the binder of `L` (originally `Type*`) is `Type v`. The audit named these universes `audit_u`, `audit_v`, `audit_w`.
