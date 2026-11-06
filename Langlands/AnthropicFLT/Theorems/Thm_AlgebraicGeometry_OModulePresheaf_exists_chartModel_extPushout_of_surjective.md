# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.solution q GE hGEc hGEq GK hGKc hGKq U₀ hU₀ r pr hpr δ`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.OModulePresheaf.exists_chartModel_extPushout_of_surjective`: let `A` be a commutative
ring, `q : P ⟶ Spec A` with `P` locally noetherian, `GE`, `GK` coherent quasi-coherent FLT presheaves over `q`, `U₀`
an affine open, `pr : Γ(P, U₀)^r → GE(U₀)` a surjection and `δ : ker pr → GK(U₀)` linear. Then there are, for every
affine open `U ⊆ U₀`: presentations `prU U : Γ(P, U)^r → GE(U)` restricting `pr` (surjective and compatible with
restriction), kernel maps `gU U : ker pr → ker (prU U)` (componentwise restriction) whose images span
`ker (prU U)`, and maps `δU U : ker (prU U) → GK(U)` with `δU U ∘ gU U = res ∘ δ`, compatible with restriction
(`_hδUn`). Moreover the pushout extensions `ExtPushout (prU U) (δU U)` (of the ported definition
`LinearMap.ExtPushout`), viewed as `A`-modules, carry restriction maps `res` that are semilinear, unital and
transitive and satisfy the basic-open localization conditions `hqc`, are finite over `Γ(P, U)`, and fit into exact
sequences `0 → GK(U) →ϑ ExtPushout →θE GE(U) → 0` compatible with restriction, where `ϑ U = inl` and
`θE U = proj`, and `res` acts on `inl` and `inr` by restriction. (The local model, over one chart, of the extension
of `GE` by `GK` with class `[δ]`; the data are in the form required by the ported theorem
`exists_isCoherent_linearEquiv_of_forall_basicOpen_of_isBasis`.)

The proof term applies the companion solution theorem
`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.OModulePresheaf.exists_chartModel_extPushout_of_surjective`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_LinearMap_ExtPushout` (same contribution), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective` (same contribution).
Other imports: `Mathlib`.
