# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist`. Statement. `AlgebraicGeometry.ProjSpace.isQuasicoherent_twist`: for `π : X ⟶ Spec A` separated and an affine
morphism `φ : X ⟶ ℙᴺ_A`, the twist `φ^* 𝒪(m)` is a quasi-coherent FLT presheaf of modules.

Proof. For an affine open `U` and `f ∈ Γ(X, U)`, the sections of the twist over `U` and over `D(f)` are
compatible families over the affine charts `U ∩ φ⁻¹ D₊(Xᵢ)` and `D(f) ∩ φ⁻¹ D₊(Xᵢ)`, the latter being the
basic opens of the image of `f`; componentwise these are localizations, and compatibility (the twisting
relations with the frame units) is preserved, so a section over `D(f)` is `x / fⁿ` and the kernel of
restriction is `f`-power torsion.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist.P2mTwistQC.restrictFun_injective_of_ge`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist.P2mTwistQC.basicOpen_restrictFun`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist.P2mTwistQC.exists_pow_mul_eq_zero`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist.P2mTwistQC.exists_restrictFun_eq_mul_pow`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist.P2mTwistQC.restrictFun_mul_pow_eq`
- abbrev `P2MW.S_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist.P2mTwistQC.V`
- abbrev `P2MW.S_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist.P2mTwistQC.V₂`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist.P2mTwistQC.isAffineOpen_V`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist.P2mTwistQC.isAffineOpen_V₂`
- abbrev `P2MW.S_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist.P2mTwistQC.fV`
- abbrev `P2MW.S_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist.P2mTwistQC.fV₂`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist.P2mTwistQC.basicOpen_fV`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist.P2mTwistQC.basicOpen_fV₂`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist.P2mTwistQC.inf_le_basicOpen_fV`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist.P2mTwistQC.basicOpen_fV_le_inf`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist.P2mTwistQC.basicOpen_fV₂_le_left`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist.P2mTwistQC.basicOpen_fV₂_le_right`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist.P2mTwistQC.basicOpen_fV₂_le_inf`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist.P2mTwistQC.torsion`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist.P2mTwistQC.z`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist.P2mTwistQC.exists_numerators`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist.P2mTwistQC.defect`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist.P2mTwistQC.restrictFun_defect_eq_zero`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist.P2mTwistQC.extension`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist.P2mTwistQC.main`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_isQuasicoherent_twist.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library).
Other imports: `Mathlib`.
