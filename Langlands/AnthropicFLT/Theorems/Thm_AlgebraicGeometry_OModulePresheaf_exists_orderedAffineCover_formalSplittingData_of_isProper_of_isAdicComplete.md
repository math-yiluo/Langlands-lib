# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.solution I q F hFc hFq φ hφs hφk E hEc hEq τ hτs hτk ε hεs hεc GE hGEc hGEq ψE hψEs hψEk hψEc GK hGKc hGKq lam hlamc hlamr hlami X hXc hXq εX hXf`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.OModulePresheaf.exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete`:
let `A` be a noetherian, `I`-adically complete commutative ring and `q : P ⟶ Spec A` proper. Take the data of the
ported theorem `exists_isCoherent_forall_ker_eq_pow_smul_top_of_extension_of_comp_eq` up to the extension: coherent
quasi-coherent adic systems `F` (maps `φ`) and `E` (maps `τ`) with compatible surjections `ε`, an algebraization
`ψE : GE → E k` of `E`, and compatible `lam k : GK → F k` with image `ker ε k` and the Artin–Rees bound `hlami`.
Let `X` be a coherent quasi-coherent presheaf with isomorphisms `εX W r p hp` from `X(W)` to the presentation
models of `Ext¹(GE(W), GK(W))`, compatible with restriction (`hXf`; as produced by the ported theorem
`exists_isCoherent_linearEquiv_extQuot_of_isCoherent`). Then there are an ordered affine cover `K` of `P`, surjective
presentations `pr i : Γ(K.U i)^(rk i) → GE(K.U i)`, compatible lifts `ℓ i n` of `ψE n ∘ pr i` along `ε n`, maps
`δs i n : ker (pr i) → GK(K.U i)` with `lam n ∘ δs i n = ℓ i n` on `ker (pr i)` and
`δs i (n+1) − δs i n ∈ (I Γ(K.U i))^(n+1) • Hom`, and Čech `0`-cochains `t n` of `X` on `K`, where `t n s` is the
restriction of the class `εX⁻¹ [δs (s 0) n]`, such that `d (t n) ∈ I^(n+1) • ⊤` and
`t (n+1) − t n ∈ I^(n+1) • ⊤`.

The proof term applies the companion solution theorem
`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.OModulePresheaf.exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover` (Library), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete` (same contribution).
Other imports: `Mathlib`.
