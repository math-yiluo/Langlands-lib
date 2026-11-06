# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq.solution I q F hFc hFq φ hφs hφk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc GK hGKc hGKq lam hlamc hlamr hlami K M res res_smul res_refl res_comp hqc hfg ϑ θE θF hϑs hθEs hθFs hϑn hθEn hθFn hexact hsurj hϑi hc1 hc2 hc3 u hub hus hun huϑ huθE hcocy huθF`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.OModulePresheaf.exists_basisData_of_chartData_of_cocycle_of_comp_eq`: let `A` be a
noetherian, `I`-adically complete commutative ring, `q : P ⟶ Spec A` proper, and take chart data on an ordered
affine cover `K` (modules `M i U`, restrictions, exact sequences `ϑ`, `θE`, maps `θF`) with overlap isomorphisms `u`
that satisfy the cocycle condition and are compatible with the chart maps (`θF j k ∘ u i j = θF i k`). Then there are
a set `B` of affine opens, closed under shrinking and covering `P`, and on it finite `Γ(P, W)`-modules `M W` (also
`A`-modules, scalar tower) with semilinear, unital, transitive restriction maps satisfying the basic-open
localization conditions, together with semilinear maps `ϑ W : GK(W) → M W`, `θE W : M W → GE(W)` and
`θF k W : M W → F k(W)`, compatible with restriction, such that `0 → GK(W) → M W → GE(W) → 0` is exact (at the middle
and on the right), `φ k ∘ θF (k+1) W = θF k W`, `θF k W ∘ ϑ W = lam k` and `ε k ∘ θF k W = ψE k ∘ θE W`. (Data in the
form required by the ported theorem `exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis`.)

The proof term applies the companion solution theorem
`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.OModulePresheaf.exists_basisData_of_chartData_of_cocycle_of_comp_eq`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq` (same contribution).
Other imports: `Mathlib`.
