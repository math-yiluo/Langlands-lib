# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf`

Ported for the proof `Langlands.AlgebraicGeometry.finiteFreeQuasiProjectiveQuotient` of `Langlands.AlgebraicGeometry.FiniteFreeQuasiProjectiveQuotientStatement` (quotients of quasi-projective schemes over a field by free actions of finite groups are quasi-projective), which depends on this module through its imports. Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf.lean` (SHA-256 `4bad7cabb52e401c6f3376d29177314e9b101dbeaa5530a8b528885f792746e0`) from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`.

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; `import Mathlib` is now `import Langlands.MathlibBase` (all of Mathlib except the three modules that clash with weil-conjectures, see `Langlands/MathlibBase.md`).
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file; it records the date of the modifications, 26 November 2026.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf`.

Statement. `AlgebraicGeometry.Scheme.exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf`:
let `V i` (`i : Fin r`) be affine opens of a scheme `Z` and let `w i j ∈ Γ(Z, V i)` satisfy `w i i = 1`,
the cocycle identity on `V i ⊓ V j` and `Z.basicOpen (w i j) = V i ⊓ V j`. Then for every `i₀` and every
section `g` over `V i₀` there is `k₀` such that for every `k ≥ k₀` there are sections `t j ∈ Γ(Z, V j)`
with `t i₀ = g` and `t j = w j m ^ k * t m` after restriction to `V j ⊓ V m`. In terms of the line bundle
on the union `⨆ i, V i` glued from the cocycle `w`: for all large `k`, the section `g` over `V i₀`
extends to a section over `⨆ i, V i` of the `k`-th tensor power of this bundle, trivialized on `V i₀`;
when the `V i` cover `Z`, this is a global section on `Z`. The theorem asserts nothing about opens
outside `⨆ i, V i`.

Proof. As `V j ⊓ V i₀ = Z.basicOpen (w j i₀)` in the affine `V j`, the ring `Γ(Z, V j ⊓ V i₀)` is the
localization of `Γ(Z, V j)` at `w j i₀`; so `w j i₀ ^ n j * g = a j` on `V j ⊓ V i₀` for some section
`a j` over `V j` (step `stepA`), with `a i₀ = g`. Multiplying by powers of `w j i₀` makes all exponents
equal to `k₁`, giving sections `b j`. On the affine `V j ⊓ V m`, the difference
`b j - w j m ^ k₁ * b m` vanishes on `V j ⊓ V m ⊓ V i₀`, the basic open of `w j i₀`, so a power
`w j i₀ ^ e j m` kills it (step `stepB`). With `E` the largest `e j m`, the sections
`t j = b j * w j i₀ ^ (k - k₁)` work for every `k ≥ k₁ + E`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Langlands.MathlibBase`.
