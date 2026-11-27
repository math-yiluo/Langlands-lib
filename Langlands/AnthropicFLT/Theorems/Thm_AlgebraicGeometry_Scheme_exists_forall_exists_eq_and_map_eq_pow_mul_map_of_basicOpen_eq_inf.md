# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf`

Ported for the proof `Langlands.AlgebraicGeometry.finiteFreeQuasiProjectiveQuotient` of `Langlands.AlgebraicGeometry.FiniteFreeQuasiProjectiveQuotientStatement` (quotients of quasi-projective schemes over a field by free actions of finite groups are quasi-projective), which depends on this module through its imports. Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf.lean` (SHA-256 `735c9b9e0ac191e5dd6a121eb6520a12eb127a1a6912e977da3bcd49288f01f9`) from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`.

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; `import Mathlib` is now `import Langlands.MathlibBase` (all of Mathlib except the three modules that clash with weil-conjectures, see `Langlands/MathlibBase.md`).
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file; it records the date of the modifications, 26 November 2026.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf.solution V hV w hW1 hW2 hW3 i₀ g`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.Scheme.exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf`:
let `V i` (`i : Fin r`) be affine opens of a scheme `Z` and let `w i j ∈ Γ(Z, V i)` satisfy `w i i = 1`,
the cocycle identity on `V i ⊓ V j` and `Z.basicOpen (w i j) = V i ⊓ V j`. Then for every `i₀` and every
section `g` over `V i₀` there is `k₀` such that for every `k ≥ k₀` there are sections `t j ∈ Γ(Z, V j)`
with `t i₀ = g` and `t j = w j m ^ k * t m` after restriction to `V j ⊓ V m`. In terms of the line bundle
on the union `⨆ i, V i` glued from the cocycle `w`: for all large `k`, the section `g` over `V i₀`
extends to a section over `⨆ i, V i` of the `k`-th tensor power of this bundle, trivialized on `V i₀`;
when the `V i` cover `Z`, this is a global section on `Z`. The theorem asserts nothing about opens
outside `⨆ i, V i`.

The proof term applies the companion solution theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf.solution`, proved in `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.Scheme.exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf`.
Other imports: `Langlands.MathlibBase`.
