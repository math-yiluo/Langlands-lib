# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app`

Ported for the proof `Langlands.AlgebraicGeometry.finiteFreeQuasiProjectiveQuotient` of `Langlands.AlgebraicGeometry.FiniteFreeQuasiProjectiveQuotientStatement` (quotients of quasi-projective schemes over a field by free actions of finite groups are quasi-projective), which depends on this module through its imports. Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app.lean` (SHA-256 `dffb3ef1b90e4e2d13359dedccf606ef3f262c349bf7f243c786bd5beafb3bb9`) from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`.

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; `import Mathlib` is now `import Langlands.MathlibBase` (all of Mathlib except the three modules that clash with weil-conjectures, see `Langlands/MathlibBase.md`).
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file; it records the date of the modifications, 26 November 2026.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app`.

Statement. `AlgebraicGeometry.Scheme.Hom.isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app`:
a morphism of schemes `φ : Y ⟶ P` is an immersion if there are affine opens `W j` of `P` whose preimages
`φ ⁻¹ᵁ W j` are affine and cover `Y`, such that every `φ.app (W j)` is surjective.

Proof. Over each `W j` the restriction `φ ∣_ W j` is a morphism of affine schemes that is surjective on
global sections, hence a closed immersion (`QPC2.isClosedImmersion_morphismRestrict_of_surjective`, via
`HasAffineProperty.iff_of_isAffine` and `morphismRestrict_appTop`). The range of `φ` lies in
`⨆ j, W j`, and being an immersion is local on the target, so `φ` is an immersion
(`IsZariskiLocalAtTarget.of_range_subset_iSup`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app.QPC2.isImmersion_respectsRight_isOpenImmersion`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app.QPC2.surjective_app_of_eq`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app.QPC2.isClosedImmersion_morphismRestrict_of_surjective`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app.QPC2.isImmersion_of_affine_charts`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Langlands.MathlibBase`.
