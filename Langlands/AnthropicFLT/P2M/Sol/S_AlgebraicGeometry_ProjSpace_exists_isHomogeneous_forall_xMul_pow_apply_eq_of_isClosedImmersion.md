# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion`. Statement. `AlgebraicGeometry.ProjSpace.exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion`: for a
closed immersion `ι : Z ⟶ ℙⁿ_A`, an element `m` of degree `e` of the twist graded module and a variable
`Xⱼ`, there are `k` and a form `F` of degree `e + k` such that `Xⱼ^k m` is given in all charts by the
dehomogenizations of `F`.

Proof (namespace `SatUnitBody`). Sections `Frac`, `Comp`: dehomogenization `frac` and its pullback
`pullAway` to the charts of `Z`, additive and multiplicative, with restriction lemmas. Section `Main`:
the transition functions are pulled-back ratios (`frameUnit_eq_pullAway`); since `ι` is a closed
immersion, the chart component `m_j` is `pullAway (F₀ / Xⱼ^a)` for a form `F₀`
(`exists_eq_pullAway_mk`); on the other charts the components agree with those of `F₀` after
multiplying by a power of the frame unit (`exists_pow_mul_eq_zero`, `basicOpen_frameUnit_le`), which is
the effect of `Xⱼ^k` (`xMul_pow_apply`, `frameUnit_pow_mul_pullAway_frac`). Take `F = Xⱼ^{k'} F₀`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion.SatUnitBody.frac`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion.SatUnitBody.val_frac`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion.SatUnitBody.frac_add`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion.SatUnitBody.frac_smul`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion.SatUnitBody.awayMap_frac_eq`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion.SatUnitBody.pullAway`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion.SatUnitBody.pullAway_eq`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion.SatUnitBody.pullAway_add`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion.SatUnitBody.pullAway_mul`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion.SatUnitBody.pullAway_zero`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion.SatUnitBody.restrictFun_pullAway_left`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion.SatUnitBody.restrictFun_pullAway_right`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion.SatUnitBody.restrictFun_pullAway_frac`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion.SatUnitBody.frameUnit_eq_pullAway`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion.SatUnitBody.xMul_pow_apply`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion.SatUnitBody.exists_eq_pullAway_mk`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion.SatUnitBody.basicOpen_frameUnit_le`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion.SatUnitBody.exists_pow_mul_eq_zero`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion.SatUnitBody.pullAway_pow`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion.SatUnitBody.frac_congr`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion.SatUnitBody.frameUnit_pow_mul_pullAway_frac`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_isHomogeneous_forall_xMul_pow_apply_eq_of_isClosedImmersion.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (same contribution).
Other imports: `Mathlib`.
