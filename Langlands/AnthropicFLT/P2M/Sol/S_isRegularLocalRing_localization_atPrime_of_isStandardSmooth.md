# `Langlands.AnthropicFLT.P2M.Sol.S_isRegularLocalRing_localization_atPrime_of_isStandardSmooth`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_isRegularLocalRing_localization_atPrime_of_isStandardSmooth.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_isRegularLocalRing_localization_atPrime_of_isStandardSmooth.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_isRegularLocalRing_localization_atPrime_of_isStandardSmooth`. Statement. `isRegularLocalRing_localization_atPrime_of_isStandardSmooth`: localizations at primes of a standard smooth algebra over a
field are regular local rings.

Proof. A standard smooth `k`-algebra has a relative dimension `m` (ported
`Algebra.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension_of_field`) and is étale over `k[X₁, …, X_m]`; the
local ring of the polynomial ring at the contracted prime is regular (ported
`isRegularLocalRing_localization_atPrime_mvPolynomial`), and regularity ascends along the étale map (ported
`isRegularLocalRing_localization_atPrime_of_etale_of_comap`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_isRegularLocalRing_localization_atPrime_of_isStandardSmooth.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_Algebra_IsStandardSmooth_exists_isStandardSmoothOfRelativeDimension_of_field` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_isRegularLocalRing_localization_atPrime_mvPolynomial` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_isRegularLocalRing_localization_atPrime_of_etale_of_comap` (same contribution).
Other imports: `Mathlib`.
