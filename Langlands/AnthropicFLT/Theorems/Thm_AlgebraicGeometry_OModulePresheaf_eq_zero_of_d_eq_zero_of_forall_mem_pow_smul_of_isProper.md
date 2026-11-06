# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper.solution I F hc hq K z hz h`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.OModulePresheaf.eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper`: let `A`
be a noetherian commutative ring, `I`-adically complete for an ideal `I`, `q : P ⟶ Spec A` proper, `F` a coherent
quasi-coherent FLT presheaf over `q`, `K` an ordered affine cover of `P`, and `z` a Čech `0`-cocycle of `F` on `K`
(`F.d K 0 z = 0`) all of whose components lie in `I^k • ⊤` for every `k`. Then `z = 0`. (Global sections of a
coherent sheaf on a proper scheme over a complete noetherian ring are `I`-adically separated.)

The proof term applies the companion solution theorem
`P2MW.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.OModulePresheaf.eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` (Library), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_eq_zero_of_d_eq_zero_of_forall_mem_pow_smul_of_isProper` (same contribution).
Other imports: `Mathlib`.
