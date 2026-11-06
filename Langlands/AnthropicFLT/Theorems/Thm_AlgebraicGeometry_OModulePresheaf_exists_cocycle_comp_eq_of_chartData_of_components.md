# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_components`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_components.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_components.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_components.solution q F φ E ε GE ψE GK lam hlamc Uc M res ϑ θE θF hϑs hθEs hθFs hϑn hθEn hθFn hexact hc1 hc2 hc3 u hub hus hun huϑ huθE hcocy zC hzCs hzCn hzCc YC hYs hYn hY tC ht hzt`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.OModulePresheaf.exists_cocycle_comp_eq_of_chartData_of_components`: an algebraic
correction step for chart data. Let `ι` be linearly ordered with opens `Uc i`, and let modules `M i U` (for affine
`U ⊆ Uc i`) carry restrictions `res`, exact sequences `0 → GK(U) →ϑ M i U →θE GE(U) → 0`, maps `θF i k U` to an
adic system `F` (compatible with `φ`, extending `lam`, compatible with `ε` and `ψE`) and overlap isomorphisms `u`
satisfying the cocycle condition. Let `zC i j` (`i < j`) be semilinear maps `GE → GK` on overlaps, compatible with
restriction and additive on triples (`zC i j + zC j l = zC i l`), `YC k i U : GE(U) → GK(U)` semilinear and
compatible with restriction with `lam k ∘ YC (k+1) = lam k ∘ YC k`, and `tC k i j` maps with
`lam k ∘ tC k i j ∘ θE = θF j k ∘ u i j − θF i k` and `lam k ∘ zC i j = lam k ∘ (tC k i j + YC k j − YC k i)`. Then
there are new maps `θF''` with the same compatibilities as `θF` and new overlap isomorphisms `u''` (bijective,
semilinear, compatible with restriction, `ϑ` and `θE`, satisfying the cocycle condition) such that the chart maps
agree on overlaps: `θF'' j k ∘ u'' i j = θF'' i k`.

The proof term applies the companion solution theorem
`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_components.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.OModulePresheaf.exists_cocycle_comp_eq_of_chartData_of_components`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_components` (same contribution).
Other imports: `Mathlib`.
