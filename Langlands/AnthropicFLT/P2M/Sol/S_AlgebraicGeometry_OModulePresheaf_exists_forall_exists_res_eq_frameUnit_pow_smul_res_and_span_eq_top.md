# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top`
(Serre's theorem A, in the frame-unit model of twists over projective space).

Proof (namespace `P2mSerreAFrames`). The charts `pullbackChart φ i`, overlaps `pullbackOverlap φ j i` and frame
units `frameUnit φ j i` are those of the Library module `Definitions.Def_AlgebraicGeometry_ProjTwistDatum`.
Section `Geometry`: the overlap `pullbackOverlap φ j i` is the basic open of `frameUnit φ j i` in the chart `j`
(`basicOpen_frameUnit`, from `proj_basicOpen_awayToSection_ratio` on `Proj`). Section `Sections`: restriction
lemmas, and the two localisation properties of the quasi-coherent `F` for this basic open (`exists_numer`,
`exists_torsion`, `exists_torsion_overlap`; the charts and overlaps are affine since `φ` is affine).

Section `Extend`. For a section `t` over the chart `i`, `ExtData` records exponents `n`, `e` and sections `y j` over
the charts `j` with `y j = u_{ji}^n t` on the overlaps (`hy`) and the discrepancies of the `y j` on the overlaps
killed by `u_{ji}^e` (`hδ`); such data exist (`exists_numer_uniform`, `exists_extData`, using the cocycle identity
`cocycle_inf` of the frame units). Then `fam q j := u_{ji}^q y j` satisfies the twisted gluing condition of degree
`n + q` once `q ≥ e` (`ExtData.fam_compat`), and `fam q i = t` (`ExtData.fam_self`).

`main`: each chart section module is finite (coherence), so choose finite generating sets `S i`; take
`ExtData` for every generator and `d₀` the maximum of `n + e`. For `d ≥ d₀`, the families
`fam (d - n)` of all generators are twisted-compatible sections of degree `d`, and their components on the chart
`i` include the generators `S i`, so they span. `solution` is `P2mSerreAFrames.main`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top.P2mSerreAFrames.proj_basicOpen_awayToSection_ratio`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top.P2mSerreAFrames.basicOpen_frameUnit`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top.P2mSerreAFrames.res_smul'`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top.P2mSerreAFrames.res_pow_smul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top.P2mSerreAFrames.res_res_eq_self`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top.P2mSerreAFrames.res_injective_of_ge`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top.P2mSerreAFrames.Uaff`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top.P2mSerreAFrames.Oaff`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top.P2mSerreAFrames.exists_numer`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top.P2mSerreAFrames.exists_torsion`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top.P2mSerreAFrames.inf_le_O`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top.P2mSerreAFrames.exists_torsion_overlap`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top.P2mSerreAFrames.inf_le_O'`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top.P2mSerreAFrames.cocycle_inf`
- structure `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top.P2mSerreAFrames.ExtData`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top.P2mSerreAFrames.exists_numer_uniform`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top.P2mSerreAFrames.exists_extData`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top.P2mSerreAFrames.ExtData.fam`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top.P2mSerreAFrames.ExtData.fam_compat`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top.P2mSerreAFrames.ExtData.fam_self`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top.P2mSerreAFrames.main`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (Library).
Other imports: `Mathlib`.
