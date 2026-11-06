# `Langlands.AnthropicFLT.P2M.Sol.S_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated`.

Proof (namespace `P2mSatSerreB`). `Saturated h` is the saturation hypothesis (every homogeneous `f` of degree `e`
has `X_j^N f = h f'` with `f'` of degree `e + N`); it is preserved by shifting the grading (`saturated_shift`,
with the degree bookkeeping `sum_add_single`). On the localized pieces of the Library Čech complex of a graded
module, the map `h.secMap I` induced by `h` (`secMap_mk`) is surjective for nonempty `I` when `h` is saturated
(a fraction `m / X^a` of `M` equals `f' / X^(a + N e_l)` for `l ∈ I`; `secMap_surjective`) and injective when `h`
is (`secMap_injective`). Since every simplex index has nonempty image (`img_nonempty`), the cochain maps
`h.cochainMap i` (`cochainMap_apply`) are bijective (`cochainMap_injective`, `cochainMap_surjective`) and commute
with the differentials (`cochainMap_d`); hence vanishing of `H^(i+1)(D)` implies that of `H^(i+1)(M)`
(`subsingleton_H_succ`). `solution`: the Library theorem `GradedModule.subsingleton_cohomology_shift_of_isFG`
(Serre vanishing for finitely presented graded modules) gives `d₀` with `H^i(D(d)) = 0` for `d ≥ d₀`, `i ≥ 1`; apply
`subsingleton_H_succ` to the shifted homomorphism `h.shift d`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated.P2mSatSerreB.Saturated`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated.P2mSatSerreB.saturated_shift`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated.P2mSatSerreB.sum_add_single`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated.P2mSatSerreB.secMap_mk`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated.P2mSatSerreB.secMap_surjective`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated.P2mSatSerreB.secMap_injective`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated.P2mSatSerreB.cochainMap_apply`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated.P2mSatSerreB.img_nonempty`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated.P2mSatSerreB.cochainMap_injective`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated.P2mSatSerreB.cochainMap_surjective`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated.P2mSatSerreB.cochainMap_d`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated.P2mSatSerreB.subsingleton_H_succ`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule` (Library), `Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_GradedModule_subsingleton_cohomology_shift_of_isFG` (Library).
Other imports: `Mathlib`.
