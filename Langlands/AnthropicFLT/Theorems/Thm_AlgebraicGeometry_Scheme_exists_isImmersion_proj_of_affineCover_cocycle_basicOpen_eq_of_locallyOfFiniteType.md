# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType`

Ported for the proof `Langlands.AlgebraicGeometry.finiteFreeQuasiProjectiveQuotient` of `Langlands.AlgebraicGeometry.FiniteFreeQuasiProjectiveQuotientStatement` (quotients of quasi-projective schemes over a field by free actions of finite groups are quasi-projective), which depends on this module through its imports. Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType.lean` (SHA-256 `2f3c49ed8146fa5f98fd7eab33b8651fa84ff7eafc71be3c345b316667adcf94`) from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`.

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; `import Mathlib` is now `import Langlands.MathlibBase` (all of Mathlib except the three modules that clash with weil-conjectures, see `Langlands/MathlibBase.md`).
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file; it records the date of the modifications, 26 November 2026.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType.solution B Y πY r V hVaff hcov w hw1 hw2 hw3`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: apart from the renames described under “Names changed by the Library” below, the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.Scheme.exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType`:
let `πY : Y ⟶ Spec B` be locally of finite type and let `Y` be covered by affine opens `V i`
(`i : Fin r`) with sections `w i j ∈ Γ(Y, V i)` such that `w i i = 1`, the cocycle identity holds on
`V i ⊓ V j` and `Y.basicOpen (w i j) = V i ⊓ V j`. Then there are `n` and an immersion
`qpι : Y ⟶ Proj B[x₀, …, x_n]` with `qpι ≫ ProjSpace.π B n = πY`. The cocycle defines a line bundle with
the sections `w j i` trivializing it on `V i`; the proof embeds `Y` by sections of a power of this
bundle.

The proof term applies the companion solution theorem `P2MW.S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType.solution`, proved in `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.Scheme.exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace`, `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType`.
Other imports: `Langlands.MathlibBase`.

## Names changed by the Library

weil-conjectures, on which the Library depends, declares 21 of the names of the FLT formalisation itself, so that no module could import both. On 22 November 2026 the Library renamed these 21 declarations: each keeps its name space and the last component of its name gets the marker `FLT` (`tensorPow` becomes `tensorPowFLT`, `tensorPow_zero` becomes `tensorPowFLT_zero`). In this file the names occur only in the `attribute [-instance]` and `attribute [-simp]` lines after the imports:

- its uses of `AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero`, `AlgebraicGeometry.Scheme.Modules.tensorPow_succ`, `AlgebraicGeometry.Scheme.Modules.tensorPow_zero`, `SheafOfModules.monoidalCategory`, `SheafOfModules.monoidalClosed` and `SheafOfModules.symmetricCategory` are written with the new names `tensorPowSectionFLT_zero`, `tensorPowFLT_succ`, `tensorPowFLT_zero`, `monoidalCategoryFLT`, `monoidalClosedFLT` and `symmetricCategoryFLT`.

Statements and proofs are otherwise unchanged. Elsewhere on this page the names are given as they now are.
