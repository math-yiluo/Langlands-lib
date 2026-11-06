# `Langlands.AnthropicFLT.P2M.Sol.S_LinearMap_forall_smul_eq_zero_and_forall_exists_eq_smul_of_ker_of_equiv_baseChange_of_flat`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_LinearMap_forall_smul_eq_zero_and_forall_exists_eq_smul_of_ker_of_equiv_baseChange_of_flat.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_LinearMap_forall_smul_eq_zero_and_forall_exists_eq_smul_of_ker_of_equiv_baseChange_of_flat.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_LinearMap_forall_smul_eq_zero_and_forall_exists_eq_smul_of_ker_of_equiv_baseChange_of_flat`.

Proof. Let `Z₀ := ker d₀` and `u₀' : L₀ → Z₀` the corestriction of `u₀`. The hypotheses say that `J` kills
`ker u₀'` and that `J` maps `Z₀` into the range of `u₀'`, so the ported theorem
`LinearMap.forall_smul_eq_zero_of_baseChange_eq_zero_and_forall_exists_baseChange_eq_smul_of_flat` gives the
same for `R ⊗ u₀'` and `J R`. By flatness, `R ⊗ Z₀ → R ⊗ C₀` is injective and `R ⊗ Z₀ → R ⊗ C₀ → R ⊗ D₀` is
exact. Transport along `eL`, `eC`, `eD` (the identities `u ∘ eL = eC ∘ (R ⊗ u₀)` and `d ∘ eC = eD ∘ (R ⊗ d₀)`
follow from `hu`, `hd` by induction on tensors). (1) If `u x = 0` with `x = eL x'`, then `(R ⊗ u₀') x' = 0` by
injectivity, so `a • x' = 0`. (2) If `d y = 0` with `y = eC y'`, then `y'` comes from `z : R ⊗ Z₀` by exactness,
and `a • z = (R ⊗ u₀') x'` gives `u (eL x') = a • y`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_LinearMap_forall_smul_eq_zero_and_forall_exists_eq_smul_of_ker_of_equiv_baseChange_of_flat.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_forall_smul_eq_zero_of_baseChange_eq_zero_and_forall_exists_baseChange_eq_smul_of_flat` (same contribution).
Other imports: `Mathlib`.
