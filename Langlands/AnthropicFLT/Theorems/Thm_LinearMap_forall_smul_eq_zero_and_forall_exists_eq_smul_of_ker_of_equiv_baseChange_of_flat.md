# `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_forall_smul_eq_zero_and_forall_exists_eq_smul_of_ker_of_equiv_baseChange_of_flat`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_LinearMap_forall_smul_eq_zero_and_forall_exists_eq_smul_of_ker_of_equiv_baseChange_of_flat.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_LinearMap_forall_smul_eq_zero_and_forall_exists_eq_smul_of_ker_of_equiv_baseChange_of_flat.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_LinearMap_forall_smul_eq_zero_and_forall_exists_eq_smul_of_ker_of_equiv_baseChange_of_flat.solution u₀ d₀ hdu₀ J hk hc u d eL eC eD hu hd`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `LinearMap.forall_smul_eq_zero_and_forall_exists_eq_smul_of_ker_of_equiv_baseChange_of_flat`: let `R`
be a flat `R₀`-algebra, `u₀ : L₀ → C₀` and `d₀ : C₀ → D₀` `R₀`-linear with `d₀ ∘ u₀ = 0`, and `J` an ideal of `R₀`
such that every `a ∈ J` kills `ker u₀` and maps `ker d₀` into the range of `u₀`. Let `u : L → C`, `d : C → D`
be `R`-linear maps identified with the base changes of `u₀`, `d₀` through isomorphisms
`eL : R ⊗ L₀ ≃ L`, `eC : R ⊗ C₀ ≃ C`, `eD : R ⊗ D₀ ≃ D` (`u (eL (1 ⊗ x)) = eC (1 ⊗ u₀ x)` and
`d (eC (1 ⊗ y)) = eD (1 ⊗ d₀ y)`). Then every `a ∈ J R` kills `ker u`, and for every `y` with `d y = 0` and
`a ∈ J R` there is `x` with `u x = a • y`.

The proof term applies the companion solution theorem
`P2MW.S_LinearMap_forall_smul_eq_zero_and_forall_exists_eq_smul_of_ker_of_equiv_baseChange_of_flat.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `LinearMap.forall_smul_eq_zero_and_forall_exists_eq_smul_of_ker_of_equiv_baseChange_of_flat`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_LinearMap_forall_smul_eq_zero_and_forall_exists_eq_smul_of_ker_of_equiv_baseChange_of_flat` (same contribution).
Other imports: `Mathlib`.
