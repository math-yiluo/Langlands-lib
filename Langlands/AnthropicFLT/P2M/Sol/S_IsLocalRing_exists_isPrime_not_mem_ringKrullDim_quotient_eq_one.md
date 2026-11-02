# `Langlands.AnthropicFLT.P2M.Sol.S_IsLocalRing_exists_isPrime_not_mem_ringKrullDim_quotient_eq_one`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_IsLocalRing_exists_isPrime_not_mem_ringKrullDim_quotient_eq_one.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof (namespace `CoheightOneGC5`).

- `eq_bot_of_height_eq_zero`: a prime of height zero in a domain is `⊥`.
- `exists_isPrime_ne_bot_ne_maximalIdeal_not_mem`: if the maximal ideal of a noetherian local domain
  has height `> 1`, then every `s ≠ 0` avoids some prime `p ≠ ⊥, 𝔪`. Otherwise every such prime
  contains `s`; then every minimal prime over `(x)`, for `x ∈ 𝔪`, has height `≤ 1` (Krull's
  principal ideal theorem `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes`) and is a
  minimal prime over `(s)`. So `𝔪` is contained in the finite union of the minimal primes over
  `(s)`, hence equals one of them by prime avoidance (`Ideal.subset_union_prime`), and has height
  `≤ 1`.
- `solution`: choose `q` maximal among the primes `≠ 𝔪` not containing `s`
  (`set_has_maximal_iff_noetherian`). In the local domain `R ⧸ q`, by maximality and the previous
  lemma, the maximal ideal has height `≤ 1`; it is nonzero since `q ≠ 𝔪`. Hence `R ⧸ q` has
  dimension `1` (`IsLocalRing.maximalIdeal_height_eq_ringKrullDim`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_IsLocalRing_exists_isPrime_not_mem_ringKrullDim_quotient_eq_one.CoheightOneGC5.eq_bot_of_height_eq_zero`
- theorem `P2MW.S_IsLocalRing_exists_isPrime_not_mem_ringKrullDim_quotient_eq_one.CoheightOneGC5.exists_isPrime_ne_bot_ne_maximalIdeal_not_mem`
- theorem `P2MW.S_IsLocalRing_exists_isPrime_not_mem_ringKrullDim_quotient_eq_one.solution`

## Dependencies

Ported FLT modules imported: none.
All modules also import `Mathlib`.
