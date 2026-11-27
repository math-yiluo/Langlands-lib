# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app`

Ported for the proof `Langlands.AlgebraicGeometry.finiteFreeQuasiProjectiveQuotient` of `Langlands.AlgebraicGeometry.FiniteFreeQuasiProjectiveQuotientStatement` (quotients of quasi-projective schemes over a field by free actions of finite groups are quasi-projective), which depends on this module through its imports. Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app.lean` (SHA-256 `8a35659b0a232d0ba3bc68fad6856376afbd14bd40cefb0b4b3d886b7fb250f7`) from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`.

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; `import Mathlib` is now `import Langlands.MathlibBase` (all of Mathlib except the three modules that clash with weil-conjectures, see `Langlands/MathlibBase.md`).
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file; it records the date of the modifications, 26 November 2026.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app.solution φ W hWaff hYaff hcov hsurj`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.Scheme.Hom.isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app`:
a morphism of schemes `φ : Y ⟶ P` is an immersion if there are affine opens `W j` of `P` whose preimages
`φ ⁻¹ᵁ W j` are affine and cover `Y`, such that every `φ.app (W j)` is surjective.

The proof term applies the companion solution theorem `P2MW.S_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app.solution`, proved in `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.Scheme.Hom.isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app`.
Other imports: `Langlands.MathlibBase`.
