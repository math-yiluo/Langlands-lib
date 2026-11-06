# `Langlands.AnthropicFLT.P2M.Sol.S_IsAdicComplete_of_finite_of_isNoetherianRing`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_IsAdicComplete_of_finite_of_isNoetherianRing.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_IsAdicComplete_of_finite_of_isNoetherianRing.solution` proves the statement of the
companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_IsAdicComplete_of_finite_of_isNoetherianRing`;
it is `SolFinComplete.isAdicComplete_of_finite`.

Proof (namespace `SolFinComplete`). `isAdicComplete_of_finite_aux` (same universe as `R`): completeness of
`M` means that `of I M : M → AdicCompletion I M` is bijective (`AdicCompletion.of_bijective_iff`). This
map factors as `M ≅ R ⊗ M ≅ R^ ⊗ M ≅ M^`, using `R ≅ R^` (completeness of `R`) and Mathlib's
`AdicCompletion.ofTensorProductEquivOfFiniteNoetherian` for finite modules over a noetherian ring.
`isAdicComplete_of_linearEquiv` transports completeness along a linear isomorphism
(`AdicCompletion.congr`). `isAdicComplete_of_finite`: a finite module `M` (in any universe) is a quotient
`(Fin n → R) ⧸ ker p`, which is complete by the auxiliary lemma, and `M` is isomorphic to it.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_IsAdicComplete_of_finite_of_isNoetherianRing.SolFinComplete.isAdicComplete_of_finite_aux`
- theorem `P2MW.S_IsAdicComplete_of_finite_of_isNoetherianRing.SolFinComplete.isAdicComplete_of_linearEquiv`
- theorem `P2MW.S_IsAdicComplete_of_finite_of_isNoetherianRing.SolFinComplete.isAdicComplete_of_finite`
- theorem `P2MW.S_IsAdicComplete_of_finite_of_isNoetherianRing.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
