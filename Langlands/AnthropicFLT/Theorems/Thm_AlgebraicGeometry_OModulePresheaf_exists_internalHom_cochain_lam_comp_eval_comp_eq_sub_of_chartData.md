# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData.solution I q F hFc hFq φ hφs hφk E ε GE hGEc hGEq ψE GK hGKc hGKq lam hlamc hlamr hlami K M res ϑ θE θF hϑs hθEs hθFs hθEn hθFn hexact hsurj hc1 hc2 hc3 u hus hun huϑ huθE`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.OModulePresheaf.exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData`:
let `A` be a noetherian commutative ring, `I` an ideal, `q : P ⟶ Spec A` proper, and take the chart data of the
ported theorem `exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete` (an ordered affine
cover `K`, modules `M i U` with restrictions `res`, exact sequences `ϑ`, `θE`, maps `θF` to the adic system `F`, and
overlap isomorphisms `u`, with all the listed compatibilities). Then there are Čech `1`-cochains `t n` of
`internalHom GE GK` on `K` with `t (n+1) − t n ∈ I^(n+1) • ⊤` such that for every `1`-simplex `s = (i₀, i₁)`, every
affine `W` inside the overlap and every `x ∈ M i₀ W`,
`lam n (t n s (θE x)) = θF i₁ n (u_{i₀i₁} x) − θF i₀ n x`. (The failure of the chart maps `θF` to agree on overlaps is
measured, `I`-adically convergently, by homomorphisms `GE → GK`.)

The proof term applies the companion solution theorem
`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.OModulePresheaf.exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom` (same contribution), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData` (same contribution).
Other imports: `Mathlib`.
