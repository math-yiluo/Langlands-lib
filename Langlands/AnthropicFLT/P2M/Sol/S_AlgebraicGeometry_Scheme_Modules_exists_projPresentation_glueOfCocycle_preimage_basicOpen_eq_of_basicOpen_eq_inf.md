# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf`

Ported for the proof `Langlands.AlgebraicGeometry.finiteFreeQuasiProjectiveQuotient` of `Langlands.AlgebraicGeometry.FiniteFreeQuasiProjectiveQuotientStatement` (quotients of quasi-projective schemes over a field by free actions of finite groups are quasi-projective), which depends on this module through its imports. Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf.lean` (SHA-256 `39e4d7c9b163145f9da1a08171d1228472a0ffa4851d43571ba72f1dd72c1cdb`) from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`.

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; `import Mathlib` is now `import Langlands.MathlibBase` (all of Mathlib except the three modules that clash with weil-conjectures, see `Langlands/MathlibBase.md`).
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file; it records the date of the modifications, 26 November 2026.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- One expression is adapted to the Library's Mathlib: `Y.sheaf.val.obj (op (⊥ : Y.Opens))` becomes `Y.sheaf.obj.obj (op (⊥ : Y.Opens))`. In the Library's Mathlib a sheaf is an object of the full subcategory of presheaves satisfying the sheaf condition, and its underlying presheaf is the field `obj` instead of `val`. The term is the same presheaf.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf`.

Statement. `AlgebraicGeometry.Scheme.Modules.exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf`:
let `πY : Y ⟶ Spec B` be a scheme over a commutative ring `B`, covered by affine opens `V i`
(`i : Fin r`) with sections `w i j ∈ Γ(Y, V i)` such that `w i i = 1` and
`Y.basicOpen (w i j) = V i ⊓ V j`. Let `k > 0` and let `c` be a unit cocycle on the `V i` with
`c.u i j = w i j ^ k` on `V i ⊓ V j`, so that `Scheme.Modules.glueOfCocycle c` is the invertible module
glued from `c`. Let `a α` (`α : Fin (N + 1)`) be families of sections `a α j ∈ Γ(Y, V j)` with
`a α j = w j m ^ k * a α m` on `V j ⊓ V m`, and let `e : Fin r → Fin (N + 1)` be injective with
`a (e i) j = w j i ^ k`. Then there is a `ProjPresentation` `𝔓` of `glueOfCocycle c` over `πY` with
`N + 1` sections whose components on the `V j` are the `a α j`, such that the morphism
`𝔓.toProj : Y ⟶ Proj B[x₀, …, x_N]` satisfies `𝔓.toProj ⁻¹ᵁ D₊(x (e i)) = V i`, and the pullback to
`V i` of the coordinate ratio `x α / x (e i)` (`ProjSpace.ratio`) is `a α i`.

Proof. Each compatible family `a α` glues to a global section `σ α` of `glueOfCocycle c`
(`GluedPres.sec`). On `V i` the section `σ (e i)` is the frame of the glued module
(`GluedPres.map_sec_eq_glueFrame`), so it generates the module on every open inside `V i`
(`GluedPres.bijective_smul_of_map_eq_glueFrame`); the indices outside the range of `e` are given the
empty open (`GluedPres.bijective_smul_bot`). The ported theorem
`AlgebraicGeometry.Scheme.Modules.exists_projPresentation_of_iSup_eq_top` then gives the presentation
`𝔓` with `V i ≤ 𝔓.toProj ⁻¹ᵁ D₊(x (e i))`. Conversely, on an open where `σ (e i)` generates, its component
`a (e i) j = w j i ^ k` is a unit (`GluedPres.inf_le_basicOpen_of_frame`), and its basic open is
`V j ⊓ V i`; this gives equality. The ratio statement follows from `𝔓.app_ratio_smul` and
`GluedPres.eq_of_smul_sec_eq`, using `a (e i) i = 1`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf.GluedPres.Compat`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf.GluedPres.sec`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf.GluedPres.glueComponent_sec`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf.GluedPres.glueComponent_map_sec`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf.GluedPres.map_sec_eq_glueFrame`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf.GluedPres.bijective_smul_of_map_eq_glueFrame`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf.GluedPres.subsingleton_sections_bot`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf.GluedPres.subsingleton_functions_bot`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf.GluedPres.bijective_smul_bot`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf.GluedPres.isUnit_of_frames`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf.GluedPres.inf_le_basicOpen_of_frame`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf.GluedPres.eq_of_smul_sec_eq`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top`.
Other imports: `Langlands.MathlibBase`.
