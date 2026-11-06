# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle.solution I q F hFc hFq φ hφs hφk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc GK hGKc hGKq lam hlamc hlamr hlami K M res res_smul res_refl res_comp hqc hfg ϑ θE θF hϑs hθEs hθFs hϑn hθEn hθFn hexact hsurj hϑi hc1 hc2 hc3 u hub hus hun huϑ huθE hcocy t ht z hz Y hzt hY`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.OModulePresheaf.exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle`: let `A` be
a noetherian, `I`-adically complete commutative ring, `q : P ⟶ Spec A` proper, and take chart data on an ordered
affine cover `K` as in the ported theorem `exists_cocycle_of_chartData_of_isProper_of_isAdicComplete` with overlap
isomorphisms `u` satisfying the cocycle condition. Let `t k` be Čech `1`-cochains of `internalHom GE GK` with
`lam k (t k s (θE x)) = θF i₁ k (u_{i₀i₁} x) − θF i₀ k x`, and let `z` be a `1`-cocycle and `Y k` `0`-cochains with
`z − t k − d (Y k) ∈ I^(k+1) • ⊤` and `Y (k+1) − Y k ∈ I^(k+1) • ⊤`. Then there are new chart maps `θF''` (with all
the compatibilities of `θF`) and new overlap isomorphisms `u''` (bijective, semilinear, compatible with restriction,
`ϑ` and `θE`, satisfying the cocycle condition) such that `θF'' j k ∘ u'' i j = θF'' i k` on overlaps.

The proof term applies the companion solution theorem
`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.OModulePresheaf.exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom` (same contribution), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle` (same contribution).
Other imports: `Mathlib`.
