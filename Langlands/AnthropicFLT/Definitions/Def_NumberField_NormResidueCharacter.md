# Dirichlet characters pulled back by the norm, and the cyclotomic image

Let K be a number field, m ≥ 1 and 𝔣_m = (m). The module gives instances that the narrow ray class group G modulo 𝔣_m is finite, with a `Fintype` structure; `nu : G →* (ℤ/m)ˣ` is the norm character. For a Dirichlet character ψ modulo m, `chi K m ψ = ψ ∘ nu`. The module proves the following.
- `chi` is multiplicative in ψ and its value at the class of a prime v not dividing m is ψ(N v).
- ψ(−1) = ±1. `paritySet ψ` is empty if ψ(−1) = 1 and consists of all real places otherwise.
- For nonzero α ≡ 1 modulo m, the value of `chiIdeal` at (α) is ψ(sign N_{K/ℚ}(α)).

Now let L/K be cyclotomic for {m} and ζ a primitive m-th root of unity in L. The module proves the following.
- Every prime of L not containing m has norm ≡ 1 modulo m.
- At most [L : K] primes of L lie above a prime of K; the same bound holds for the fibres of the map v ↦ v ∩ K on height-one primes.
- A prime of L whose norm is a rational prime has the same norm as the prime of K below it.

Let U₀ ⊆ (ℤ/m)ˣ be the image of Gal(L/K) under the cyclotomic character `autToPow`; then #U₀ = [L : K]. Using Mathlib's arithmetic Frobenius at a prime of L above v, the module proves that the norm class of every prime v of K lies in U₀ (`normClass_mem_U0`). Hence the image of `nu` lies in U₀.

Source: `Definitions/Def_NumberField_NormResidueCharacter.lean` (entire file, 351 lines) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `aac3ba8897030aa84892ecc6e8cbf8f0ae6d3147dd541cbbf71539efd34af941`. Declaration names and namespaces are unchanged.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the proof `Langlands.Global.chebotarevPrimeRealizationStatement` in `Langlands/Global/Arithmetic/ChebotarevPrimeRealizationProof.lean`.

Port changes: imports of FLT modules use the `Langlands.AnthropicFLT` prefix; the source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set after the imports; the audit's modification comments are replaced by the port header. Apart from the universe generalization, the mathematical hypotheses and conclusions of the source are retained.

The following edits of the audit `notes/reuse/anthropic-chebotarev-audit.md` are applied. Its evidence files `compatibility.md`, `universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact diffs.

- Compatibility with Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435` (the source pins Lean 4.33.1 and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`): in `normClass_mem_U0`, the step `simpa [h2, hζ.coe_toInteger] using h` became `change φ ζ = ζ ^ Ideal.absNorm v.asIdeal at h; exact h`, which exposes the coercion of the integral primitive root definitionally.
- Universes: `universe u v w` is declared; the binder of `K` (originally `Type`) is `Type u`; the binder of `L` (originally `Type`) is `Type v`. The audit named these universes `audit_u`, `audit_v`, `audit_w`.
