# `Langlands.AnthropicFLT.P2M.Sol.S_LinearMap_exists_isBaseChange_ker_span_range_eq_top_of_flat`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_LinearMap_exists_isBaseChange_ker_span_range_eq_top_of_flat.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Compatibility edit for the project's Mathlib: in the proof of `mem_span_of_isBaseChange`, the case `| zero => exact Submodule.zero_mem _` of `induction y using hf.inductionOn` is deleted. In this Mathlib, `IsBaseChange.inductionOn` has only the cases `tmul`, `smul` and `add`, so Lean rejects the `zero` case. The other cases are unchanged.

## Content

The theorem `P2MW.S_LinearMap_exists_isBaseChange_ker_span_range_eq_top_of_flat.solution` proves the statement of the
companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_isBaseChange_ker_span_range_eq_top_of_flat`.

Proof. Helpers (`PresBCSol`): `φ n : R^n → S^n` (componentwise `algebraMap`, `φ_apply`) is a base change
(`isBaseChange_φ`), and the image of a base change spans the target (`mem_span_of_isBaseChange`). `solution`:
`g : ker p → ker p'` is the restriction of `φ r` (it lands in `ker p'` because `p' ∘ φ r = μ ∘ p`); Mathlib's
`IsBaseChange.of_left_exact` (using flatness of `B'` and exactness of `0 → ker p → B^r → M` and its base change)
shows that `g` is a base change, and therefore its image spans `ker p'`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_LinearMap_exists_isBaseChange_ker_span_range_eq_top_of_flat.PresBCSol.φ`
- theorem `P2MW.S_LinearMap_exists_isBaseChange_ker_span_range_eq_top_of_flat.PresBCSol.φ_apply`
- theorem `P2MW.S_LinearMap_exists_isBaseChange_ker_span_range_eq_top_of_flat.PresBCSol.isBaseChange_φ`
- theorem `P2MW.S_LinearMap_exists_isBaseChange_ker_span_range_eq_top_of_flat.PresBCSol.mem_span_of_isBaseChange`
- theorem `P2MW.S_LinearMap_exists_isBaseChange_ker_span_range_eq_top_of_flat.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
