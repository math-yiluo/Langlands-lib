# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback`. Statement. `AlgebraicGeometry.ProjSpace.exists_linearEquiv_baseChange_cochain_twist_of_isPullback`: let `ι : Z ⟶ ℙⁿ_A`
and `ι' : Z' ⟶ ℙⁿ_B` be affine, `Z'` the base change of `Z` along `Spec B ⟶ Spec A` (compatibly with
`ProjSpace.map`). Then for every `d` the Čech cochains of the twist `𝒪_{Z'}(d)` are `B ⊗[A]` the cochains
of `𝒪_Z(d)`: there are `B`-linear isomorphisms `ε i`, compatible with the differentials, sending
`1 ⊗ c` to the pullback of `c` along `e`.

Proof. On each chart the twist is trivialized by the ported
`ProjSpace.exists_linearEquiv_twistObj_of_le_pullbackChart`; the intersections of the pulled-back
cover are affine, and those of `Z'` are the base changes of those of `Z` (ported
`ProjSpace.map_preimage_basicOpen_X`), so their sections satisfy `Γ(Z', W') ≅ B ⊗[A] Γ(Z, W)` (ported
`Scheme.isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback`). Taking products over the
finitely many index tuples gives `ε i`; compatibility with the differentials holds because both
sides are computed by restrictions and the frame units, which are pulled back.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback.P2mWs6C3.preimage_pullbackChart`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback.P2mWs6C3.preimage_inter`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback.P2mWs6C3.inter_le_pullbackChart`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback.P2mWs6C3.isAffineOpen_inter`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback.P2mWs6C3.X_eq_mvMapGraded_mul_one`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback.P2mWs6C3.one_mem_zero`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback.P2mWs6C3.toB`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback.P2mWs6C3.toB_ratio`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback.P2mWs6C3.restrictFun_app_pullAway`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback.P2mWs6C3.restrictFun_app_frameUnit`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback.P2mWs6C3.restrictFun_app_eq`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback.P2mWs6C3.appLE_top_top`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback.P2mWs6C3.appLE_hom_apply`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback.P2mWs6C3.valAddHom`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback.P2mWs6C3.val_sum`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback.P2mWs6C3.val_zsmul`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback.P2mWs6C3.val_sum'`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback.P2mWs6C3.val_zsmul'`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_isAffineOpen_and_exists_linearEquiv_tensor_sections_of_isPullback` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_map_preimage_basicOpen_X` (Library).
Other imports: `Mathlib`.
