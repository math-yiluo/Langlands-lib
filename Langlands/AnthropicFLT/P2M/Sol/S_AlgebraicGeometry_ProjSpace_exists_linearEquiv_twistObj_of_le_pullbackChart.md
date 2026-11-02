# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart`. Statement. `AlgebraicGeometry.ProjSpace.exists_linearEquiv_twistObj_of_le_pullbackChart`: on an open `W` contained in
the chart `φ⁻¹ D₊(Xᵢ)`, the sections of the twist `φ^* 𝒪(m)` are isomorphic to `Γ(X, W)` as a
`Γ(X, W)`-module, by taking the `i`-th component; the inverse sends `a` to the family
`((Xᵢ/Xⱼ)^m a)ⱼ` (built from the frame units `frameUnit φ j i`).

Proof. The `i`-th component map is linear; the family `j ↦ (frameUnit φ j i)^m · a` is compatible by the
cocycle identities of the frame units (`frameUnit_cocycle`, `frameUnit_self`), and the two maps are
inverse: a compatible family is determined by its `i`-th component on `W ⊆ φ⁻¹ D₊(Xᵢ)`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart.P2mTwistChartTriv.le_inf_chart`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart.P2mTwistChartTriv.res_down_up`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart.P2mTwistChartTriv.res_up_down`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart.P2mTwistChartTriv.fwd`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart.P2mTwistChartTriv.fwd_apply`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart.P2mTwistChartTriv.invVal`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart.P2mTwistChartTriv.cocycle_res`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart.P2mTwistChartTriv.invVal_compat`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart.P2mTwistChartTriv.inv`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart.P2mTwistChartTriv.inv_val`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart.P2mTwistChartTriv.fwd_inv`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart.P2mTwistChartTriv.inv_fwd`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart.P2mTwistChartTriv.equiv`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart.P2mTwistChartTriv.equiv_apply`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart.P2mTwistChartTriv.equiv_symm_apply`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart.P2mTwistChartTriv.main`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (same contribution).
Other imports: `Mathlib`.
