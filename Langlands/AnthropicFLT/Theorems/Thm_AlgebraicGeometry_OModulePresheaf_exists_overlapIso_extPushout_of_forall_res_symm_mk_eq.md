# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.solution q GE hGEc hGEq GK hGKc hGKq X hXc hXq εX hXf K rk pr hpr δ hδ prU _hprU _hprUs _hprUn gU _hgU δU _hδU _hgUspan _hδUn res res_add res_inl res_inr`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.OModulePresheaf.exists_overlapIso_extPushout_of_forall_res_symm_mk_eq`: let `A` be a
commutative ring, `q : P ⟶ Spec A` separated with `P` locally noetherian, `GE`, `GK` coherent quasi-coherent, and
`X` a coherent quasi-coherent model of `Ext¹(GE, GK)` (isomorphisms `εX` to presentation models, compatible with
restriction, `hXf`). Let `K` be an ordered affine cover with presentations `pr i` of `GE` on the charts and maps
`δ i : ker (pr i) → GK(U_i)` whose `Ext¹` classes agree on every affine `W ⊆ U_i ∩ U_j` (`hδ`), and let `prU`, `gU`,
`δU` and `res` be the chart data of the ported theorem `exists_chartModel_extPushout_of_surjective` for each chart
(with `res` additive and acting on `inl`, `inr` by restriction). Then there are `A`-linear bijections
`u i j W hj : ExtPushout (prU i W) (δU i W) → ExtPushout (prU j W) (δU j W)` for affine `W ⊆ U_i ∩ U_j`,
`Γ(P, W)`-semilinear, compatible with `res`, sending `inl x` to `inl x` and commuting with `proj`. (The local
extensions on two charts with the same class are isomorphic over the overlap, as extensions.)

The proof term applies the companion solution theorem
`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.OModulePresheaf.exists_overlapIso_extPushout_of_forall_res_symm_mk_eq`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_LinearMap_ExtPushout` (same contribution), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq` (same contribution).
Other imports: `Mathlib`.
