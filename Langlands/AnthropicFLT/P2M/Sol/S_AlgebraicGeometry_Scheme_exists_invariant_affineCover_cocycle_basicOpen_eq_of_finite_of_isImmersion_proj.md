# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj`

Ported for the proof `Langlands.AlgebraicGeometry.finiteFreeQuasiProjectiveQuotient` of `Langlands.AlgebraicGeometry.FiniteFreeQuasiProjectiveQuotientStatement` (quotients of quasi-projective schemes over a field by free actions of finite groups are quasi-projective), which depends on this module through its imports. Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj.lean` (SHA-256 `7a4e0e99052903574addc0014afb092cdc1045ed72270f0e441f7db84113ba4c`) from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`.

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; `import Mathlib` is now `import Langlands.MathlibBase` (all of Mathlib except the three modules that clash with weil-conjectures, see `Langlands/MathlibBase.md`).
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file; it records the date of the modifications, 26 November 2026.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT text writes `(ρ γ).hom` for the morphism underlying an automorphism `ρ γ : Aut X`, as in the Mathlib that FLT uses, where `Aut X` is `X ≅ X`. In the Library's Mathlib `CategoryTheory.Aut X` is a structure whose underlying isomorphism is the field `asIso`, so each of the 25 occurrences of `(ρ …).hom` is written `(ρ …).asIso.hom`. Both denote the same morphism; nothing else in the statements and proofs is changed by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj`.

Statement. `AlgebraicGeometry.Scheme.exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj`:
let `B` be a commutative ring, `X` a quasi-compact scheme and `πX : X ⟶ Spec B` a morphism that is an
immersion into some `Proj` of the polynomial ring `B[x₀, …, x_m]` followed by its structure morphism
`ProjSpace.π B m`, and let a finite group `Γ` act on `X` over `Spec B` through `ρ : Γ →* Aut X`. Then
`X` has a finite cover by affine opens `U i` (`i : Fin r`), each invariant under every `ρ γ`, with sections
`w i j ∈ Γ(X, U i)` satisfying `w i i = 1`, the cocycle identity on `U i ⊓ U j` and
`X.basicOpen (w i j) = U i ⊓ U j`, and invariant under every `ρ γ`.

Proof. For every point `x`, the theorem
`AlgebraicGeometry.exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj`
applied to the orbit of `x` gives a homogeneous `F x` of positive degree `d x` such that the affine open
`ι ⁻¹ᵁ D₊(F x)` contains every `ρ γ x`. The invariant opens `O x = ⨅ γ, (ρ γ) ⁻¹ᵁ ι ⁻¹ᵁ D₊(F x)`
contain `x`, and quasi-compactness of `X` gives finitely many points `c i` with `⨆ i, O (c i) = ⊤`
(`A2Asm.exists_fin_cover`). The powers `G i = F (c i) ^ (D / d (c i))` have the common degree
`D = ∏ i, d (c i)` and `D₊(G i) = D₊(F (c i))`. The theorem
`AlgebraicGeometry.Proj.exists_cocycle_basicOpen_eq_inf_of_mem_of_pos` gives a cocycle on the opens
`D₊(G i)`, `AlgebraicGeometry.Scheme.Hom.app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf`
pulls it back to the opens `ι ⁻¹ᵁ D₊(G i)`, and
`AlgebraicGeometry.Scheme.exists_invariant_cocycle_basicOpen_eq_iInf_preimage_of_finite` turns it into an
invariant cocycle on `U i = ⨅ γ, (ρ γ) ⁻¹ᵁ ι ⁻¹ᵁ D₊(G i) = O (c i)`. These opens cover `X`; they are
affine as finite intersections of affine opens, since `πX` is separated, being an immersion followed by
the separated `ProjSpace.π B m` (`A2Asm.isSeparated_of_isImmersion_proj`,
`A2Asm.isAffineOpen_finset_inf`). The hypothesis that the action is over `Spec B` is not used by the
proof.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj.A2Asm.isAffineOpen_inf_of_isSeparated`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj.A2Asm.mem_finset_inf`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj.A2Asm.isAffineOpen_finset_inf`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj.A2Asm.preimage_finset_univ_inf_eq`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj.A2Asm.isSeparated_of_isImmersion_proj`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj.A2Asm.exists_fin_cover`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj.A2Asm.proj_basicOpen_pow`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_invariant_affineCover_cocycle_basicOpen_eq_of_finite_of_isImmersion_proj.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Proj_exists_cocycle_basicOpen_eq_inf_of_mem_of_pos`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_invariant_cocycle_basicOpen_eq_iInf_preimage_of_finite`.
Other imports: `Langlands.MathlibBase`.
