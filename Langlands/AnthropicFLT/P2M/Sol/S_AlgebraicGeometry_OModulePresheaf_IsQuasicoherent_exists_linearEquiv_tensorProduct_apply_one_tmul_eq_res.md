# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res`:
for `G` quasi-coherent and affine opens `V ⊆ U`, the map `θ : Γ(X, V) ⊗[Γ(X, U)] G(U) → G(V)`,
`b ⊗ x ↦ b • x|_V`, is an isomorphism.

Proof (namespace `P2mQcSubAffine`). `mem_of_forall_pow_smul_mem` is the partition-of-unity lemma: if a
finite set `T` generates the unit ideal and some power of each `t ∈ T` moves `y` into a submodule `N'`, then
`y ∈ N'`. The section `RingFacts` collects facts on the restriction maps `rf` between rings of sections
(composition `rf_rf`; `exists_pow_mul_eq_zero`: an element vanishing on a basic open `D(g)` is killed by a
power of `g`; `exists_pow_mul_eq_rf`: a section over `D(g)` times a power of `g` comes from the affine open).
The map `θ` (`theta`) is `LinearMap.liftBaseChange` of the restriction `resLin`. The restrictions to `V` of
the `r ∈ Γ(X, U)` with `D(r) ⊆ V` generate the unit ideal of `Γ(X, V)` (`span_eq_top`, `exists_finset`).
For such `r`, a power of `r` moves every element of the tensor product to an element `1 ⊗ x'`
(`exists_pow_mul_eq_res`, `exists_pow_smul_eq_one_tmul`). FLT quasi-coherence of `G` says that
`G(U) → G(D(r))` is a localisation at `r`. This gives, after multiplication by a power of `r`, injectivity
and surjectivity of `θ`, and the partition-of-unity lemma removes the powers (`theta_injective`,
`theta_surjective`). `main` packages `θ` as a linear equivalence, and `solution` applies it.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res.P2mQcSubAffine.mem_of_forall_pow_smul_mem`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res.P2mQcSubAffine.rf`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res.P2mQcSubAffine.rf_rf`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res.P2mQcSubAffine.exists_pow_mul_eq_zero`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res.P2mQcSubAffine.exists_pow_mul_eq_rf`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res.P2mQcSubAffine.exists_pow_smul_eq_zero`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res.P2mQcSubAffine.resLin`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res.P2mQcSubAffine.theta`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res.P2mQcSubAffine.theta_tmul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res.P2mQcSubAffine.span_eq_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res.P2mQcSubAffine.exists_finset`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res.P2mQcSubAffine.exists_pow_mul_eq_res`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res.P2mQcSubAffine.exists_pow_smul_eq_one_tmul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res.P2mQcSubAffine.theta_injective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res.P2mQcSubAffine.theta_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res.P2mQcSubAffine.main`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` (Library).
Other imports: `Mathlib`.
