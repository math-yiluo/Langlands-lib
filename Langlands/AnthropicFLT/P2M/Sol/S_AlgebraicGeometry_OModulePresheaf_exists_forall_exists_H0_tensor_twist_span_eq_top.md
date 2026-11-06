# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top`.

Proof (namespace `P2mSerreAH0Bridge`): translation of the frame-unit form of Serre's theorem A into Čech `H0` of
`F ⊗ O(d)`, with the twist `ProjSpace.twist` and the cover `ProjSpace.stdCoverPullback ι` of the Library.
`frameSec i W` is the frame section of the twist over an open `W` inside the chart `i` (components
`u_{ki}^d`); every section of the twist over such `W` is a multiple of it (`exists_eq_smul_frameSec`), it is
compatible with restriction (`res_frameSec`), and frame sections of two charts differ by `u_{ij}^d`
(`frameSec_eq_smul`). For a family `t` of chart sections, `secOn t i W := t i|_W ⊗ frameSec i W`; if `t` satisfies
the degree-`d` twisted gluing condition (`Compat`), these agree for different charts (`secOn_eq`). The chart of a
`0`-simplex of the cover is `ch s` (`inter_le_chart`, `chart_le_inter`), so `cochainOf t` is a Čech `0`-cochain,
a cocycle when `t` is compatible (`d_cochainOf`, `cocycleOf`), and generating chart families give generating
cochain components (`span_eq_top`). `main`: the ported theorem
`exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top` (for the closed immersion `ι`, which is
affine) gives `d₀` and, for `d ≥ d₀`, compatible generating families `t l`; their `cocycleOf` are the required
elements `σ l` of `H0`. `solution` is `P2mSerreAH0Bridge.main`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top.P2mSerreAH0Bridge.frameSec`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top.P2mSerreAH0Bridge.frameSec_val`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top.P2mSerreAH0Bridge.exists_eq_smul_frameSec`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top.P2mSerreAH0Bridge.res_frameSec`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top.P2mSerreAH0Bridge.frameSec_eq_smul`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top.P2mSerreAH0Bridge.Compat`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top.P2mSerreAH0Bridge.secOn`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top.P2mSerreAH0Bridge.res_secOn`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top.P2mSerreAH0Bridge.secOn_eq`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top.P2mSerreAH0Bridge.ch`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top.P2mSerreAH0Bridge.inter_le_chart`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top.P2mSerreAH0Bridge.chart_le_inter`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top.P2mSerreAH0Bridge.inter_le_chart'`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top.P2mSerreAH0Bridge.cochainOf`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top.P2mSerreAH0Bridge.cochainOf_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top.P2mSerreAH0Bridge.d_cochainOf`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top.P2mSerreAH0Bridge.cocycleOf`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top.P2mSerreAH0Bridge.res_res_eq_self`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top.P2mSerreAH0Bridge.span_eq_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top.P2mSerreAH0Bridge.main`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafTensor` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart` (Library).
Other imports: `Mathlib`.
