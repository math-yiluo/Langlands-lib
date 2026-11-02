# `Langlands.AnthropicFLT.P2M.Sol.S_ProjSpaceCech_GradedModule_Presentation_forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_ProjSpaceCech_GradedModule_Presentation_forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_ProjSpaceCech_GradedModule_Presentation_forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_GradedModule_Presentation_forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one`. Statement. `ProjSpaceCech.GradedModule.Presentation.forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one`: let
`0 → K → F → D → 0` be a presentation of a graded module `D` and `d ∈ ℤ`. If `H¹` of the twist `K(d)` vanishes and every
`H⁰` class of `F(d)` is given by an element of `F` of degree `d`, then every `H⁰` class of `D(d)` is given by an element of
`D` of degree `d`.

Proof. The Čech complexes form a short exact sequence (`secMap_shift_surjective`, ported
`ProjSpaceCech.GradedModule.Hom.secMap_injective`, `ProjSpaceCech.GradedModule.d_sq`). A cocycle of `D(d)` in degree
zero lifts to a cochain of `F(d)` whose coboundary lies in `K(d)` and is a cocycle there, hence a coboundary since
`H¹(K(d)) = 0`; correcting the lift gives a cocycle of `F(d)`, which comes from an element of `F` of degree `d`; its image in
`D` represents the class (`exists_secMap_kerIncl_eq_of_secMap_eq_zero`, `secMap_secMap_kerIncl`, `cochainMap_apply`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_ProjSpaceCech_GradedModule_Presentation_forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one.SESBody.secMap_mk`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_Presentation_forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one.SESBody.cochainMap_apply`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_Presentation_forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one.SESBody.secMap_shift_surjective`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_Presentation_forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one.SESBody.exists_secMap_kerIncl_eq_of_secMap_eq_zero`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_Presentation_forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one.SESBody.secMap_secMap_kerIncl`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_Presentation_forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule` (Library), `Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_GradedModule_d_sq` (Library), `Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_GradedModule_Hom_secMap_injective` (same contribution).
Other imports: `Mathlib`.
