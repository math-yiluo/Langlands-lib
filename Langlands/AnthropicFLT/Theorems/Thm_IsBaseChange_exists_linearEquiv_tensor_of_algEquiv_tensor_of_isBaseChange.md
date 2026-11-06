# `Langlands.AnthropicFLT.Theorems.Thm_IsBaseChange_exists_linearEquiv_tensor_of_algEquiv_tensor_of_isBaseChange`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_IsBaseChange_exists_linearEquiv_tensor_of_algEquiv_tensor_of_isBaseChange.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_IsBaseChange_exists_linearEquiv_tensor_of_algEquiv_tensor_of_isBaseChange.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_IsBaseChange_exists_linearEquiv_tensor_of_algEquiv_tensor_of_isBaseChange.solution ψ θ hθ₁ hθ₂ eL f₀ hf₀ f hf`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `IsBaseChange.exists_linearEquiv_tensor_of_algEquiv_tensor_of_isBaseChange`: let `R`, `Γ₀`, `S` be
`R₀`-algebras with `S` an `R`-algebra, `ψ : Γ₀ → S` an `R₀`-algebra map and `θ : Γ₀ ⊗[R₀] R ≃ S` an `R₀`-algebra
isomorphism with `θ (a ⊗ 1) = ψ a` and `θ (1 ⊗ r) = r`. Let `eL : R ⊗[R₀] L₀ ≃ L` be `R`-linear, `f₀ : L₀ → N₀` a
base change along `R₀ → Γ₀`, and `f : L → N` an `R`-linear base change along `R → S`. Then there is an `R`-linear
isomorphism `Φ : R ⊗[R₀] N₀ ≃ N` with `Φ (1 ⊗ f₀ x₀) = f (eL (1 ⊗ x₀))` and
`Φ (r ⊗ γ • n₀) = r • (ψ γ • Φ (1 ⊗ n₀))`; moreover two `R`-linear maps out of `R ⊗[R₀] N₀` that agree on all
`r ⊗ (γ • f₀ x₀)` are equal.

The proof term applies the companion solution theorem
`P2MW.S_IsBaseChange_exists_linearEquiv_tensor_of_algEquiv_tensor_of_isBaseChange.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `IsBaseChange.exists_linearEquiv_tensor_of_algEquiv_tensor_of_isBaseChange`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_IsBaseChange_exists_linearEquiv_tensor_of_algEquiv_tensor_of_isBaseChange` (same contribution).
Other imports: `Mathlib`.
