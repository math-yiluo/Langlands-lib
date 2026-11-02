# `Langlands.AnthropicFLT.P2M.Sol.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_shift_eq_sec_mk_of_isFG`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_ProjSpaceCech_GradedModule_exists_forall_H_zero_shift_eq_sec_mk_of_isFG.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_shift_eq_sec_mk_of_isFG.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_GradedModule_exists_forall_H_zero_shift_eq_sec_mk_of_isFG`. Statement. `ProjSpaceCech.GradedModule.exists_forall_H_zero_shift_eq_sec_mk_of_isFG`: for a finitely generated graded module `D` over
`R[x₀, …, x_n]` with `R` noetherian, there is `d₀` such that for `d ≥ d₀` every class in the Čech `H⁰` of `D(d)` is
represented by an element of `D` of degree `d`.

Proof. Choose a presentation `F → D` with kernel `K`, finitely generated since `R` is noetherian (ported
`ProjSpaceCech.GradedModule.Presentation.ker_isFG`). For large `d`, `H¹(K(d)) = 0` (ported
`ProjSpaceCech.GradedModule.subsingleton_cohomology_shift_of_isFG`) and `H⁰(F(d))` is represented by elements of `F`
(ported `ProjSpaceCech.GradedModule.exists_forall_H_zero_pi_FD_shift_eq_sec_mk`); conclude with the ported
`ProjSpaceCech.GradedModule.Presentation.forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_ProjSpaceCech_GradedModule_exists_forall_H_zero_shift_eq_sec_mk_of_isFG.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule` (Library), `Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_GradedModule_Presentation_forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_GradedModule_exists_forall_H_zero_pi_FD_shift_eq_sec_mk` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_GradedModule_subsingleton_cohomology_shift_of_isFG` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_GradedModule_Presentation_ker_isFG` (Library).
Other imports: `Mathlib`.
