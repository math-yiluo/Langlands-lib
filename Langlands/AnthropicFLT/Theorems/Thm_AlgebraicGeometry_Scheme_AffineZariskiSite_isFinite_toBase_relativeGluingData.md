# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_AffineZariskiSite_isFinite_toBase_relativeGluingData`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_Scheme_AffineZariskiSite_isFinite_toBase_relativeGluingData.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_AffineZariskiSite_isFinite_toBase_relativeGluingData.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_Scheme_AffineZariskiSite_isFinite_toBase_relativeGluingData.solution H hfin`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.Scheme.AffineZariskiSite.isFinite_toBase_relativeGluingData`: let `F` be a
functor from the opposite of the affine Zariski site of a scheme `X` to commutative rings, with a natural
transformation `α : 𝒪_X → F` (on affine opens) that is coequifibered (`H`), so that the spectra `Spec F(U)`
glue to a scheme over `X` (Mathlib's `relativeGluingData H`). If every `α U : Γ(X, U) → F(U)` is a finite
ring map, the structure morphism `(relativeGluingData H).toBase` of the glued scheme to `X` is finite.

The proof term applies the companion solution theorem
`P2MW.S_AlgebraicGeometry_Scheme_AffineZariskiSite_isFinite_toBase_relativeGluingData.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.Scheme.AffineZariskiSite.isFinite_toBase_relativeGluingData`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_AffineZariskiSite_isFinite_toBase_relativeGluingData` (same contribution).
Other imports: `Mathlib`.
