# `Langlands.AnthropicFLT.Theorems.Thm_IsLocalizedModule_exists_forall_apply_eq_of_span_range_eq_top`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_IsLocalizedModule_exists_forall_apply_eq_of_span_range_eq_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_IsLocalizedModule_exists_forall_apply_eq_of_span_range_eq_top.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_IsLocalizedModule_exists_forall_apply_eq_of_span_range_eq_top.solution g hg f l l' hll x hx`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `IsLocalizedModule.exists_forall_apply_eq_of_span_range_eq_top`: let `R` be a commutative ring, `M` an
`R`-module and `g : ι → R` a finite family generating the unit ideal. Let `f i : M → N i` be localizations of `M` at
the powers of `g i`, and `l i j : N i → N₂ i j` localizations at the powers of `g j`, with maps
`l' i j : N j → N₂ i j` such that `l i j ∘ f i = l' i j ∘ f j`. Then every family `x i ∈ N i` that is compatible
(`l i j (x i) = l' i j (x j)` for all `i, j`) comes from a single element: there is `m ∈ M` with `f i m = x i` for
all `i`. (The existence half of the sheaf property of `M~` for a finite cover by basic opens.)

The proof term applies the companion solution theorem
`P2MW.S_IsLocalizedModule_exists_forall_apply_eq_of_span_range_eq_top.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `IsLocalizedModule.exists_forall_apply_eq_of_span_range_eq_top`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_IsLocalizedModule_exists_forall_apply_eq_of_span_range_eq_top` (same contribution).
Other imports: `Mathlib`.
