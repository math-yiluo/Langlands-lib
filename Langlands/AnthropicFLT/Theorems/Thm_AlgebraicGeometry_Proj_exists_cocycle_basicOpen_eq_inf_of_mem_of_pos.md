# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Proj_exists_cocycle_basicOpen_eq_inf_of_mem_of_pos`

Ported for the proof `Langlands.AlgebraicGeometry.finiteFreeQuasiProjectiveQuotient` of `Langlands.AlgebraicGeometry.FiniteFreeQuasiProjectiveQuotientStatement` (quotients of quasi-projective schemes over a field by free actions of finite groups are quasi-projective), which depends on this module through its imports. Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_Proj_exists_cocycle_basicOpen_eq_inf_of_mem_of_pos.lean` (SHA-256 `f263b90df4d1eb81477d7cf022247e4656f7507d75aa6f1b156730808667c9af`) from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`.

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; `import Mathlib` is now `import Langlands.MathlibBase` (all of Mathlib except the three modules that clash with weil-conjectures, see `Langlands/MathlibBase.md`).
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file; it records the date of the modifications, 26 November 2026.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Proj_exists_cocycle_basicOpen_eq_inf_of_mem_of_pos.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_Proj_exists_cocycle_basicOpen_eq_inf_of_mem_of_pos.solution 𝒜 hd F hF`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.Proj.exists_cocycle_basicOpen_eq_inf_of_mem_of_pos`: let `𝒜` be an
`ℕ`-graded ring and let `F i ∈ 𝒜 d` (`i : Fin r`) be homogeneous of one positive degree `d`. Then the
opens `D₊(F i)` of `Proj 𝒜` are affine, and there are sections `w i j` of `Proj 𝒜` over `D₊(F i)` with
`w i i = 1`, `w i k = w i j * w j k` after restriction to `D₊(F i) ⊓ D₊(F j)`, and
`(Proj 𝒜).basicOpen (w i j) = D₊(F i) ⊓ D₊(F j)`; namely `w i j = F j / F i`.

The proof term applies the companion solution theorem `P2MW.S_AlgebraicGeometry_Proj_exists_cocycle_basicOpen_eq_inf_of_mem_of_pos.solution`, proved in `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Proj_exists_cocycle_basicOpen_eq_inf_of_mem_of_pos`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.Proj.exists_cocycle_basicOpen_eq_inf_of_mem_of_pos`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Proj_exists_cocycle_basicOpen_eq_inf_of_mem_of_pos`.
Other imports: `Langlands.MathlibBase`.
