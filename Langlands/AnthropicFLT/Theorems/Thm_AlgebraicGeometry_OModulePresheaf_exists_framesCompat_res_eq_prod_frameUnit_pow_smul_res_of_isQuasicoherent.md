# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.solution ι G hq c d t`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.OModulePresheaf.exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent`:
let `A` be a commutative ring, `ι : P ⟶ ℙ^r_A` an affine morphism, `q : P ⟶ Spec A`, `G` a quasi-coherent FLT
presheaf over `q`, `c : Fin (i+1) → Fin (r+1)` a choice of charts and `t` a section of `G` over
`W = ⋂_v ι⁻¹ D₊(X_{c v})`. Then for every `d` there are `N` and a family `t' j` of sections over the charts
`ι⁻¹ D₊(X_j)` satisfying the twisted gluing condition `FramesCompat` in degree `d + N(i+1)`, such that on
`ι⁻¹ D₊(X_j) ∩ W` the section `t' j` restricts to `(∏_v u_{j, c v})^N · u_{j, c 0}^d · t` (with `u` the frame units).
(A section of `G(d)` over an intersection of charts, multiplied by a high power of `X_{c 0} ⋯ X_{c i}`, extends to a
global section of a higher twist.)

The proof term applies the companion solution theorem
`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.OModulePresheaf.exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafFamilyFramesGradedModule` (same contribution), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent` (same contribution).
Other imports: `Mathlib`.
