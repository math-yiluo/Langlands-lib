# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_tensorPowSection_smul_monoidalV2`

Ported for the projective representability of the relative endomorphism functor of a projective abelian scheme. Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_Scheme_Modules_tensorPowSection_smul_monoidalV2.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`.

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; `import Mathlib` is now `import Langlands.MathlibBase` (all of Mathlib except the three modules that clash with weil-conjectures, see `Langlands/MathlibBase.md`).
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_tensorPowSection_smul_monoidalV2.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_Scheme_Modules_tensorPowSection_smul_monoidalV2.solution g s n`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: apart from the renames described under “Names changed by the Library” below, the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.Scheme.Modules.tensorPowSection_smul_monoidalV2`: `(g · s)^{⊗n} = gⁿ · s^{⊗n}` for a function
`g` and a section `s` over `U`.

The proof term applies the companion solution theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_tensorPowSection_smul_monoidalV2.solution`.

## Declarations

Names, namespaces and statements are the FLT ones, apart from the renames described under “Names changed by the Library” below.

- theorem `AlgebraicGeometry.Scheme.Modules.tensorPowSection_smul_monoidalV2`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_PresheafOfModules_InternalHom` (Library), `Langlands.AnthropicFLT.Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf` (Library), `Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_MonoidalV2` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2` (Library), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_tensorPowSection_smul_monoidalV2` (ported with this file).
Other imports: `Langlands.MathlibBase`.

## Names changed by the Library (22 November 2026)

weil-conjectures, on which the Library depends, declares 21 of the names of this extract itself, so that no module could import both. The Library renamed these 21 declarations: each keeps its name space and the last component of its name gets the marker `FLT` (`tensorPow` becomes `tensorPowFLT`, `tensorPow_zero` becomes `tensorPowFLT_zero`). In this file:

- its uses of `AlgebraicGeometry.Scheme.Modules.tensorPowSection` are uses of `tensorPowSectionFLT` now.

Statements and proofs are otherwise unchanged. Elsewhere on this page the names are given as they now are.
