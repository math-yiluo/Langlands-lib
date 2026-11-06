# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_forall_isAffineOpen_basicOpen`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_forall_isAffineOpen_basicOpen.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_forall_isAffineOpen_basicOpen.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_forall_isAffineOpen_basicOpen`.

Proof (namespace `K72W5b`). `sheafAffine`: for `G` quasi-coherent over a separated `Y ⟶ Spec R`, an ordered
affine cover `K` and an affine open `Wa`, sections over `Wa` are determined by their restrictions to the
`K.U j ⊓ Wa`, and compatible families on these glue (from the ported
`bijective_cechPushforward_of_isAffineOpen_preimage` with `p = 𝟙`). Section `Cover`: `KY` is the ordered
affine cover of `Y` by the preimages under `t` of the charts over `W` (`iSup_preimage_chart_eq_top`).
Section `Functions`: `fn sY U r` is the image of `r : R` in `Γ(Y, U)` (`map_fn`, `basicOpen_fn`, `fn_smul`,
`fn_pow_smul`, `res_eq_zero_iff_of_eq`).

`solution`: fix `a` in the vanishing ideal and let `Ya` be the basic open of its image `aR`, affine by `hYa`.
(1) If `ε x` vanishes on every chart preimage, then by `sheafAffine` (separation on `Ya`) `ε Ya x = 0`, so
`a^k • x = 0` by `hKa`. (2) A compatible family `c` restricts to a compatible family on the `KY.U j ⊓ Ya`,
which glues to `z : G (Ya)` by `sheafAffine`; `hCa` gives `x` and `k` with `ε Ya x = aR^k • z`. On each affine
member `KY.U j`, `ε x - aR^k • c j` vanishes on the basic open of `aR`, so by quasi-coherence it is killed by
`aR^(n j)`. Then `k' := Σ n j + k` and `x' := a^(Σ n j) • x` satisfy `ε x' = aR^k' • c j` on every chart.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_forall_isAffineOpen_basicOpen.K72W5b.sheafAffine`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_forall_isAffineOpen_basicOpen.K72W5b.KY`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_forall_isAffineOpen_basicOpen.K72W5b.iSup_preimage_chart_eq_top`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_forall_isAffineOpen_basicOpen.K72W5b.fn`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_forall_isAffineOpen_basicOpen.K72W5b.fn_eq_algebraMap`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_forall_isAffineOpen_basicOpen.K72W5b.map_fn`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_forall_isAffineOpen_basicOpen.K72W5b.basicOpen_fn`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_forall_isAffineOpen_basicOpen.K72W5b.fn_smul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_forall_isAffineOpen_basicOpen.K72W5b.fn_pow_smul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_forall_isAffineOpen_basicOpen.K72W5b.res_eq_zero_iff_of_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_forall_isAffineOpen_basicOpen.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_bijective_cechPushforward_of_isAffineOpen_preimage` (same contribution).
Other imports: `Mathlib`.
