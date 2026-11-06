# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_forall_basicOpen_quasicoherent_of_forall_exists_linearEquiv_tensorProduct`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_forall_basicOpen_quasicoherent_of_forall_exists_linearEquiv_tensorProduct.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_basicOpen_quasicoherent_of_forall_exists_linearEquiv_tensorProduct.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_basicOpen_quasicoherent_of_forall_exists_linearEquiv_tensorProduct`.

Proof. Let `D := D(f) ⊆ V` (affine; `Γ(V', D)` is the localisation of `Γ(V', V)` at `f`). By `hβ`, the maps
`η k U₀ V` and `η k U₀ D` are base changes along `Γ(P, U₀) → Γ(V', V)` and `Γ(P, U₀) → Γ(V', D)`; by `hηV` the
restriction `ρ : F' k (V) → F' k (D)` composed with the first is the second. Hence `ρ` is a base change along
`Γ(V', V) → Γ(V', D)` (`IsBaseChange.of_comp`), i.e. a localisation at the powers of `f`
(`isLocalizedModule_iff_isBaseChange`). The two properties are the surjectivity and kernel descriptions of a
localisation map (`IsLocalizedModule.surj`, `IsLocalizedModule.eq_zero_iff`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_forall_basicOpen_quasicoherent_of_forall_exists_linearEquiv_tensorProduct.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library).
Other imports: `Mathlib`.
