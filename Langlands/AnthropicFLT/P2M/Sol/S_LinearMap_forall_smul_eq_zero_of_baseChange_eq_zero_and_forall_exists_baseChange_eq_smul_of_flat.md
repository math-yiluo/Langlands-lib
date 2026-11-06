# `Langlands.AnthropicFLT.P2M.Sol.S_LinearMap_forall_smul_eq_zero_of_baseChange_eq_zero_and_forall_exists_baseChange_eq_smul_of_flat`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_LinearMap_forall_smul_eq_zero_of_baseChange_eq_zero_and_forall_exists_baseChange_eq_smul_of_flat.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_LinearMap_forall_smul_eq_zero_of_baseChange_eq_zero_and_forall_exists_baseChange_eq_smul_of_flat.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_LinearMap_forall_smul_eq_zero_of_baseChange_eq_zero_and_forall_exists_baseChange_eq_smul_of_flat`.

Proof. (1) Since `R` is flat over `R₀`, `R ⊗ ker u → R ⊗ M → R ⊗ N` is exact (`Module.Flat.lTensor_exact`),
so an element `x` with `(R ⊗ u) x = 0` comes from some `z : R ⊗ ker u`. Every `j ∈ J` kills `R ⊗ ker u`
(induction on tensors, from `hk`), so `J` lies in the preimage of the annihilator of `x`, and therefore
`J R` kills `x` (`Ideal.map_le_iff_le_comap`, `Ideal.torsionOf`). (2) It suffices that `(J R) • ⊤` lies in the
range of `R ⊗ u`; after restricting scalars to `R₀` this is `J • ⊤ ≤ range`, checked on tensors `r ⊗ n` with
`hc`: `j • (r ⊗ n) = r ⊗ u x`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_LinearMap_forall_smul_eq_zero_of_baseChange_eq_zero_and_forall_exists_baseChange_eq_smul_of_flat.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
