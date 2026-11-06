# `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_existsUnique_sub_eq_comp_comp_of_extension`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_LinearMap_existsUnique_sub_eq_comp_comp_of_extension.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_LinearMap_existsUnique_sub_eq_comp_comp_of_extension.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_LinearMap_existsUnique_sub_eq_comp_comp_of_extension.solution ϑ θ ϑ' θ' hθ hex hϑ' hex' α β hK hE`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `LinearMap.existsUnique_sub_eq_comp_comp_of_extension`: let `R` be a commutative ring,
`K →ϑ M →θ E` and `K →ϑ' M' →θ' E` linear maps with `θ` surjective, `range ϑ = ker θ`, `ϑ'` injective and
`range ϑ' = ker θ'`. If `α, β : M → M'` agree on `K` (`α ∘ ϑ = β ∘ ϑ`) and over `E` (`θ' ∘ α = θ' ∘ β`), then there is a
unique `γ : E → K` with `α − β = ϑ' ∘ γ ∘ θ`. (Two morphisms of extensions of `E` by `K` differ by a map `E → K`.)

The proof term applies the companion solution theorem
`P2MW.S_LinearMap_existsUnique_sub_eq_comp_comp_of_extension.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `LinearMap.existsUnique_sub_eq_comp_comp_of_extension`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_LinearMap_existsUnique_sub_eq_comp_comp_of_extension` (same contribution).
Other imports: `Mathlib`.
