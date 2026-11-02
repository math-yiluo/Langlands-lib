# `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_AlgebraicGeometry_ProjTwistDatum.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Pullbacks of the twisting sheaves `𝒪(m)` of projective space, described by transition functions
(namespace `AlgebraicGeometry.ProjSpace`), for a morphism `φ : X ⟶ ℙᴺ_A` (FLT's `Proj` of the
standard graded polynomial ring) and `π : X ⟶ Spec A`.

- Chart identities in `ℙᴺ_A`: `val_awayMap_ratio`, `awayMap_ratio_mul` (on `D₊(XᵢXᵢ')` the ratios
  satisfy `(Xᵢ'/Xᵢ)(Xⱼ/Xᵢ') = Xⱼ/Xᵢ`) and `awayMap_ratio_mul_swap`.
- `pullbackChart φ i = φ⁻¹ D₊(Xᵢ)`, `frameUnit φ i j ∈ Γ(X, φ⁻¹ D₊(Xᵢ))` (the pullback of `Xⱼ/Xᵢ`),
  `restrictFun` (restriction maps of the structure sheaf), and `TwistCompat φ m U g`: a family of
  sections `gᵢ` over `U ∩ φ⁻¹ D₊(Xᵢ)` satisfies `gᵢ = (Xⱼ/Xᵢ)^m · gⱼ` on the triple overlaps;
  `twistSections φ m U`, the additive subgroup of such families, closed under multiplication by
  sections over `U` and under restriction (`smul_mem_twistSections`, `res_mem_twistSections`), with
  restriction lemmas `restrictFun_restrictFun`, `restrictFun_irrel`, `restrictFun_refl`,
  `restrictFun_algebraMap`, `restrictFun_algebraMap'`.
- `twistObj π φ m U` (a structure: such a compatible family), with `equivSections`, its additive
  group, `Γ(X, U)`-module and `A`-module structures (`smul_val`, `algebraMap_smul`, `add_val`,
  `zero_val`), restriction maps `twistRes` (`twistRes_val`), and `twist π φ m`, the resulting FLT
  `OModulePresheaf π` (`twist_obj`, `twist_res_val`, `twist_smul_val`, `twist_algebraMap_smul_val`):
  the sections of `φ^* 𝒪(m)` written in the charts.
- Overlaps: `pullbackOverlap φ i i' = φ⁻¹ D₊(XᵢXᵢ')` (`pullbackOverlap_eq_inf` and the inclusions),
  `restrictFun_frameUnit_left`, `restrictFun_frameUnit_right`, the cocycle identity
  `frameUnit_cocycle`, `frameUnit_self` (`= 1`), `frameUnit_mul_swap`, and
  `isUnit_restrictFun_frameUnit` (the transition functions are units on the overlaps).
- Section `GradedModuleOfTwist`: `twistFam π φ` (families indexed by `d ∈ ℤ` and the charts) with
  its `A`-module structure, the graded pieces `twistGrade φ π d` (supported in degree `d`, zero for
  `d < 0`, compatible for exponent `d`), the multiplication by `Xⱼ` maps `twistXMul φ π j` (raising
  the degree by one, `twistXMul_mem`; they commute, `twistXMul_comm`), and the graded module
  `twistGradedModule φ π : ProjSpaceCech.GradedModule A N` (with `_M`, `_grade`, `_xMul` lemmas);
  `twistGradeToObj`, `objToTwistFam` and the `A`-linear isomorphism
  `twistGradeEquiv φ π hd : twistGrade φ π d ≃ₗ[A] twistObj π φ d.toNat ⊤` for `d ≥ 0`.
- For affine `φ`: `pullbackChart_eq_stdCoverPullback_U`, `isAffineOpen_pullbackChart`,
  `isAffineOpen_pullbackOverlap`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.ProjSpace.val_awayMap_ratio`
- theorem `AlgebraicGeometry.ProjSpace.awayMap_ratio_mul`
- theorem `AlgebraicGeometry.ProjSpace.awayMap_ratio_mul_swap`
- def `AlgebraicGeometry.ProjSpace.pullbackChart`
- theorem `AlgebraicGeometry.ProjSpace.pullbackChart_eq`
- def `AlgebraicGeometry.ProjSpace.frameUnit`
- abbrev `AlgebraicGeometry.ProjSpace.restrictFun`
- def `AlgebraicGeometry.ProjSpace.TwistCompat`
- def `AlgebraicGeometry.ProjSpace.twistSections`
- theorem `AlgebraicGeometry.ProjSpace.mem_twistSections`
- theorem `AlgebraicGeometry.ProjSpace.smul_mem_twistSections`
- theorem `AlgebraicGeometry.ProjSpace.res_mem_twistSections`
- theorem `AlgebraicGeometry.ProjSpace.restrictFun_restrictFun`
- theorem `AlgebraicGeometry.ProjSpace.restrictFun_irrel`
- theorem `AlgebraicGeometry.ProjSpace.restrictFun_refl`
- theorem `AlgebraicGeometry.ProjSpace.restrictFun_algebraMap`
- theorem `AlgebraicGeometry.ProjSpace.restrictFun_algebraMap'`
- structure `AlgebraicGeometry.ProjSpace.twistObj`
- def `AlgebraicGeometry.ProjSpace.twistObj.equivSections`
- instance `AlgebraicGeometry.ProjSpace.twistObj.addCommGroup`
- theorem `AlgebraicGeometry.ProjSpace.twistObj.val_injective`
- instance `AlgebraicGeometry.ProjSpace.twistObj.moduleSections`
- theorem `AlgebraicGeometry.ProjSpace.twistObj.smul_val`
- instance `AlgebraicGeometry.ProjSpace.twistObj.module`
- theorem `AlgebraicGeometry.ProjSpace.twistObj.algebraMap_smul`
- def `AlgebraicGeometry.ProjSpace.twistRes`
- theorem `AlgebraicGeometry.ProjSpace.twistRes_val`
- def `AlgebraicGeometry.ProjSpace.twist`
- theorem `AlgebraicGeometry.ProjSpace.twist_obj`
- def `AlgebraicGeometry.ProjSpace.pullbackOverlap`
- theorem `AlgebraicGeometry.ProjSpace.pullbackOverlap_eq_inf`
- theorem `AlgebraicGeometry.ProjSpace.pullbackOverlap_le_left`
- theorem `AlgebraicGeometry.ProjSpace.pullbackOverlap_le_right`
- theorem `AlgebraicGeometry.ProjSpace.restrictFun_frameUnit_left`
- theorem `AlgebraicGeometry.ProjSpace.restrictFun_frameUnit_right`
- theorem `AlgebraicGeometry.ProjSpace.frameUnit_cocycle`
- theorem `AlgebraicGeometry.ProjSpace.frameUnit_self`
- theorem `AlgebraicGeometry.ProjSpace.frameUnit_mul_swap`
- theorem `AlgebraicGeometry.ProjSpace.twistObj.add_val`
- theorem `AlgebraicGeometry.ProjSpace.twistObj.zero_val`
- theorem `AlgebraicGeometry.ProjSpace.twist_res_val`
- theorem `AlgebraicGeometry.ProjSpace.twist_smul_val`
- theorem `AlgebraicGeometry.ProjSpace.twist_algebraMap_smul_val`
- def `AlgebraicGeometry.ProjSpace.twistFam`
- instance `AlgebraicGeometry.ProjSpace.twistFam.addCommGroup`
- def `AlgebraicGeometry.ProjSpace.moduleOfHom`
- instance `AlgebraicGeometry.ProjSpace.twistFam.module`
- theorem `AlgebraicGeometry.ProjSpace.twistFam.smul_apply`
- def `AlgebraicGeometry.ProjSpace.twistGrade`
- def `AlgebraicGeometry.ProjSpace.twistXMul`
- theorem `AlgebraicGeometry.ProjSpace.twistXMul_apply`
- theorem `AlgebraicGeometry.ProjSpace.frameUnit_cocycle_top`
- theorem `AlgebraicGeometry.ProjSpace.twistXMul_mem`
- theorem `AlgebraicGeometry.ProjSpace.twistXMul_comm`
- def `AlgebraicGeometry.ProjSpace.twistGradedModule`
- theorem `AlgebraicGeometry.ProjSpace.twistGradedModule_M`
- theorem `AlgebraicGeometry.ProjSpace.twistGradedModule_grade`
- theorem `AlgebraicGeometry.ProjSpace.twistGradedModule_xMul`
- def `AlgebraicGeometry.ProjSpace.twistGradeToObj`
- theorem `AlgebraicGeometry.ProjSpace.twistGradeToObj_val`
- def `AlgebraicGeometry.ProjSpace.objToTwistFam`
- theorem `AlgebraicGeometry.ProjSpace.objToTwistFam_mem`
- theorem `AlgebraicGeometry.ProjSpace.isUnit_restrictFun_frameUnit`
- theorem `AlgebraicGeometry.ProjSpace.pullbackChart_eq_stdCoverPullback_U`
- theorem `AlgebraicGeometry.ProjSpace.isAffineOpen_pullbackChart`
- theorem `AlgebraicGeometry.ProjSpace.isAffineOpen_pullbackOverlap`
- def `AlgebraicGeometry.ProjSpace.twistGradeEquiv`
- theorem `AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule` (Library).
Other imports: `Mathlib`.
