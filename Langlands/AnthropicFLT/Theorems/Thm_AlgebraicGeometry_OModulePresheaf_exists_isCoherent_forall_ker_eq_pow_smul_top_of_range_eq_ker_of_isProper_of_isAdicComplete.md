# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete.solution I q E hEc hEq τ hτs hτk Ps hPsc hPsq π hπs hπk Cs hCsc hCsq γ hγs hγk θ hθc u huc hur hui GP hGPc hGPq ψP hψPs hψPk hψPc GC hGCc hGCq ψC hψCs hψCk hψCc`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete`:
let `A` be a noetherian commutative ring, `I`-adically complete, and `q : P ⟶ Spec A` proper. Let `E`, `Ps`, `Cs` be
coherent quasi-coherent adic systems of FLT presheaves over `q` (transition maps `τ`, `π`, `γ`, surjective on
affine opens with kernels `I^(k+1) • ⊤`), with compatible maps `θ k : Ps k → Cs k` and `u k : E k → Ps k` such that
`range (u k) = ker (θ k)` on affines and, on each affine `U`, `ker (u (k+c)) ≤ I^(k+1) • ⊤` for some `c` and all
`k`. Assume `Ps` and `Cs` are the adic systems of coherent quasi-coherent presheaves `GP` and `GC` (surjections
`ψP k : GP → Ps k`, `ψC k : GC → Cs k` on affines with kernels `I^(k+1) • ⊤`, compatible with the transition maps).
Then there are a coherent quasi-coherent `G` and maps `ψ k : AffHom G (E k)`, surjective on affines with kernel
`I^(k+1) • ⊤` and compatible with `τ`: the adic system `E`, approximately the kernel of `θ`, is algebraisable.

The proof term applies the companion solution theorem
`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_range_eq_ker_of_isProper_of_isAdicComplete` (same contribution).
Other imports: `Mathlib`.
