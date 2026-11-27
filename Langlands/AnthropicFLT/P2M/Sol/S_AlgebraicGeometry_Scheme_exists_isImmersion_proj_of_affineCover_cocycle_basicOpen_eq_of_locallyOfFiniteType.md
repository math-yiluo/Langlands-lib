# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType`

Ported for the proof `Langlands.AlgebraicGeometry.finiteFreeQuasiProjectiveQuotient` of `Langlands.AlgebraicGeometry.FiniteFreeQuasiProjectiveQuotientStatement` (quotients of quasi-projective schemes over a field by free actions of finite groups are quasi-projective), which depends on this module through its imports. Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType.lean` (SHA-256 `6942ca190b929affe233c04d0f839c0e615cc797539fb5042c9b4484a16f6026`) from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`.

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; `import Mathlib` is now `import Langlands.MathlibBase` (all of Mathlib except the three modules that clash with weil-conjectures, see `Langlands/MathlibBase.md`).
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file; it records the date of the modifications, 26 November 2026.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType`.

Statement. `AlgebraicGeometry.Scheme.exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType`:
let `πY : Y ⟶ Spec B` be locally of finite type and let `Y` be covered by affine opens `V i`
(`i : Fin r`) with sections `w i j ∈ Γ(Y, V i)` such that `w i i = 1`, the cocycle identity holds on
`V i ⊓ V j` and `Y.basicOpen (w i j) = V i ⊓ V j`. Then there are `n` and an immersion
`qpι : Y ⟶ Proj B[x₀, …, x_n]` with `qpι ≫ ProjSpace.π B n = πY`. The cocycle defines a line bundle with
the sections `w j i` trivializing it on `V i`; the proof embeds `Y` by sections of a power of this
bundle.

Proof. Each ring `Γ(Y, V i)` is a finitely generated `B`-algebra (`AmpleChartsAux.finiteType_φ`);
choose finite sets of generators `s i` (`AmpleChartsAux.exists_finset_forall_surjective`). By
`AlgebraicGeometry.Scheme.exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf`, for one
large `k` every generator `x ∈ s i` extends to a compatible family `t x` for the cocycle `w ^ k`. Let
`M` be the number of generators counted with their chart index (pairs `(i, x)` with `x ∈ s i`) and
`N = r + M`. The `r` frame families `j ↦ w j i ^ k` (`i : Fin r`), the `M` families `t x` and one zero
family, indexed by `Fin (N + 1)`, are `N + 1` compatible families, and
`AlgebraicGeometry.Scheme.Modules.exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf`
gives a morphism `𝔓.toProj : Y ⟶ Proj B[x₀, …, x_N]` over `Spec B` with
`𝔓.toProj ⁻¹ᵁ D₊(x (e i)) = V i`, under which the coordinate ratios pull back to these families. So the
ring map from the chart `D₊(x (e i))` to `Γ(Y, V i)` has every generator in `s i` in its image, and it is
surjective. The theorem
`AlgebraicGeometry.Scheme.Hom.isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app`
then shows that `𝔓.toProj` is an immersion.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType.AmpleChartsAux.exists_finset_forall_surjective`
- def `P2MW.S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType.AmpleChartsAux.φ`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType.AmpleChartsAux.fromSpec_comp`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType.AmpleChartsAux.finiteType_φ`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType.AmpleChartsAux.SpecMap_awayToSection_comp_awayι`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app`.
Other imports: `Langlands.MathlibBase`.
