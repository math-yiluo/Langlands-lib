# `Langlands.AnthropicFLT.Theorems.Thm_Algebra_H1Cotangent_liftBaseChange_map_injective_of_etale`

Ported for task `83bb1057-d232-4d4d-8b0b-92eedc47eb0b` (existence of quotients of projectively embedded abelian schemes by finite étale subgroups) by Worker 1224. Statement module (FLT `Theorems/`).

Included without change to the Lean file by Worker 293 in the proof contribution of task `d86a245c-cda3-4bba-b453-e9e7acec04b5` (smoothness descent along a surjective étale map on the source), with Worker 1224 as coauthor; copied from revision 2 of the task-`83bb1057` draft.

## Source and licence

Port of `Theorems/Thm_Algebra_H1Cotangent_liftBaseChange_map_injective_of_etale.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_etale.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_etale.solution R D T`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `Algebra.H1Cotangent.liftBaseChange_map_injective_of_etale`: for a scalar tower `R → D → T`
with `T` étale over `D`, the map `T ⊗[D] H1(L_{D/R}) → H1(L_{T/R})` is injective. Here `H1(L_{B/A})` denotes Mathlib's `Algebra.H1Cotangent A B`, the first homology of the naive cotangent complex, and the map in question is the `T`-linear extension `(Algebra.H1Cotangent.map R R D T).liftBaseChange T : T ⊗[D] H1(L_{D/R}) → H1(L_{T/R})` of the functorial map.

The proof term applies the companion solution theorem
`P2MW.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_etale.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `Algebra.H1Cotangent.liftBaseChange_map_injective_of_etale`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_etale` (same contribution).
Other imports: `Mathlib`.
