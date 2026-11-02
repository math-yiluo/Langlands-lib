# `Langlands.AnthropicFLT.P2M.Sol.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_etale`

Ported for task `83bb1057-d232-4d4d-8b0b-92eedc47eb0b` (existence of quotients of projectively embedded abelian schemes by finite étale subgroups) by Worker 1224. Proof module (FLT `P2M/Sol/`).

Included without change to the Lean file by Worker 293 in the proof contribution of task `d86a245c-cda3-4bba-b453-e9e7acec04b5` (smoothness descent along a surjective étale map on the source), with Worker 1224 as coauthor; copied from revision 2 of the task-`83bb1057` draft.

## Source and licence

Port of `P2M/Sol/S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_etale.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `solution` proves the statement of `Algebra.H1Cotangent.liftBaseChange_map_injective_of_etale`
(companion module `Langlands.AnthropicFLT.Theorems.Thm_Algebra_H1Cotangent_liftBaseChange_map_injective_of_etale`):
for `R → D → T` with `T` étale over `D`, `T ⊗[D] H1(L_{D/R}) → H1(L_{T/R})` is injective.

Proof. The elements `t` of `T` with `T_t` standard étale over `D` generate the unit ideal
(`Algebra.IsEtaleAt.exists_isStandardEtale` at each maximal ideal). For such `t`, a standard étale
presentation gives `T_t ≅ D[X, Y]/(f(X), g(X)·Y − 1)` with `f` monic. The auxiliary lemma
`EtaleH1GC7.isWeaklyRegular_pair` shows that `(C g · X − 1, C f)` is weakly regular in `B[X]` when `f` is a
non-zero-divisor of `B` (here `B = D[X]`; regularity of `f` on `B[X]/(gX − 1) ≅ B[1/g]`),
`isWeaklyRegular_pair_mv` transports this to `MvPolynomial (Fin 2) D`, and weak regularity is kept after
localisation at maximal ideals (flat base change). The ported
`Algebra.injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular` then
applies.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_etale.EtaleH1GC7.isWeaklyRegular_pair`
- theorem `P2MW.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_etale.EtaleH1GC7.isWeaklyRegular_pair_mv`
- theorem `P2MW.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_etale.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular` (same contribution).
Other imports: `Mathlib`.
