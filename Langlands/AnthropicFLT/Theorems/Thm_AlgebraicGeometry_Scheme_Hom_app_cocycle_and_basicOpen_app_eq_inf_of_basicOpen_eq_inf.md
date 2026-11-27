# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf`

Ported for the proof `Langlands.AlgebraicGeometry.finiteFreeQuasiProjectiveQuotient` of `Langlands.AlgebraicGeometry.FiniteFreeQuasiProjectiveQuotientStatement` (quotients of quasi-projective schemes over a field by free actions of finite groups are quasi-projective), which depends on this module through its imports. Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_Scheme_Hom_app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf.lean` (SHA-256 `77e870c05b65239bd9dc000763d97f6c6466704dbdfd028ea6a8793fae70cb6e`) from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`.

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; `import Mathlib` is now `import Langlands.MathlibBase` (all of Mathlib except the three modules that clash with weil-conjectures, see `Langlands/MathlibBase.md`).
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file; it records the date of the modifications, 26 November 2026.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_Scheme_Hom_app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf.solution f V w hW1 hW2 hW3`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.Scheme.Hom.app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf`: let
`f : X ⟶ Z` be a morphism of schemes and let `w i j ∈ Γ(Z, V i)` (`i j : Fin r`) satisfy `w i i = 1`,
the cocycle identity `w i k = w i j * w j k` after restriction to `V i ⊓ V j`, and
`Z.basicOpen (w i j) = V i ⊓ V j`. Then the pullbacks `f.app (V i) (w i j)` satisfy the same three
identities for the opens `f ⁻¹ᵁ V i` of `X`.

The proof term applies the companion solution theorem `P2MW.S_AlgebraicGeometry_Scheme_Hom_app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf.solution`, proved in `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.Scheme.Hom.app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf`.
Other imports: `Langlands.MathlibBase`.
