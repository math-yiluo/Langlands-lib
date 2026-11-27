# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf`

Ported for the proof `Langlands.AlgebraicGeometry.finiteFreeQuasiProjectiveQuotient` of `Langlands.AlgebraicGeometry.FiniteFreeQuasiProjectiveQuotientStatement` (quotients of quasi-projective schemes over a field by free actions of finite groups are quasi-projective), which depends on this module through its imports. Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf.lean` (SHA-256 `7e61106120925756a8ff86d9f3b9d45fe1487e9d4d350c7e2f4d56ebbdc79777`) from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`.

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; `import Mathlib` is now `import Langlands.MathlibBase` (all of Mathlib except the three modules that clash with weil-conjectures, see `Langlands/MathlibBase.md`).
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file; it records the date of the modifications, 26 November 2026.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf.solution B Y πY r V hVaff hcov w hw1 hw3 k hk c hc N a ha e he hae`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

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

The proof term applies the companion solution theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf.solution`, proved in `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.Scheme.Modules.exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle`, `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf`.
Other imports: `Langlands.MathlibBase`.
