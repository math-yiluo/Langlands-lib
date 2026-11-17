# Ideal and prime Dirichlet sums with values in [0, ∞]

For a number field K and real s, the module defines `normRpow K s I = N(I)^(−s)` in [0, ∞] and the following sums of these terms.
- `idealSum K s`: the sum over nonzero ideals.
- `primeSum K s`: the sum over height-one primes.
- `primeSqSum K s`: the sum of the squares over height-one primes.
- `factoredSum K T s`: the sum over ideals supported on a finite set T of primes (`IsFactoredBy`).
- `degOneSum`: the sum of degree-one counts over rational primes outside a finite set S₀; `cutSum` is its complement on S₀.
- `tailSum K s`: the sum over height-one primes whose absolute norm is not a prime number.
- `tailConst = Σ_p p^(−2)`: the sum over rational primes.

It also defines `primeFactors I`. For a height-one prime v it defines `ratBelow v`, the rational prime below v. It proves that `ratBelow v` is prime and gives an instance that v lies over it. Finally it defines the ideal counts `idealCount n` (ideals of norm n) and the terms `zetaTerm`.

Source: `Definitions/Def_FrobeniusDensity_PrimeSums.lean` (entire file, 95 lines) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `ea0a4763273524c436940a2b95811a9cb7b4900b1ff63d3127d8b17579178644`. Declaration names and namespaces are unchanged.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the proof `Langlands.Global.chebotarevPrimeRealizationStatement` in `Langlands/Global/Arithmetic/ChebotarevPrimeRealizationProof.lean`.

Port changes: imports of FLT modules use the `Langlands.AnthropicFLT` prefix; the source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set after the imports; the audit's modification comments are replaced by the port header. Apart from the universe generalization, the mathematical hypotheses and conclusions of the source are retained.

The following edits of the audit `notes/reuse/anthropic-chebotarev-audit.md` are applied. Its evidence files `compatibility.md`, `universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact diffs.

- Universes: `universe u v w` is declared; the binder of `K` (originally `Type*`) is `Type u`. The audit named these universes `audit_u`, `audit_v`, `audit_w`.
