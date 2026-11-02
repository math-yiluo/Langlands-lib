# `Langlands.AnthropicFLT.P2M.Sol.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_smooth`

Ported for task `83bb1057-d232-4d4d-8b0b-92eedc47eb0b` (existence of quotients of projectively embedded abelian schemes by finite étale subgroups) by Worker 1224. Proof module (FLT `P2M/Sol/`).

Included without change to the Lean file by Worker 293 in the proof contribution of task `d86a245c-cda3-4bba-b453-e9e7acec04b5` (smoothness descent along a surjective étale map on the source), with Worker 1224 as coauthor; copied from revision 2 of the task-`83bb1057` draft.

## Source and licence

Port of `P2M/Sol/S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_smooth.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_reactivate "N"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N` with the same namespaces, which activates the same scoped extensions: `P2MW.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_smooth.JZInj`.
- The FLT file ends with the diagnostic command `#print axioms solution`, which only prints the axioms used and adds nothing to the environment; the port drops it.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `solution` proves the statement of `Algebra.H1Cotangent.liftBaseChange_map_injective_of_smooth`
(companion module `Langlands.AnthropicFLT.Theorems.Thm_Algebra_H1Cotangent_liftBaseChange_map_injective_of_smooth`):
for `R → S → T` with `T` smooth over `S`, `T ⊗[S] H1(L_{S/R}) → H1(L_{T/R})` is injective.

Proof (namespace `JZInj`).
- `poly_step`: the case `T = MvPolynomial (Fin n) S`. With `R' = MvPolynomial (Fin n) R`, `polyEquiv`
  identifies `R' ⊗[R] S` with `MvPolynomial (Fin n) S`; flat base change of `H1`
  (`Algebra.tensorH1CotangentOfFlat`) and the comparison maps then show the map is injective.
- `chart_step`: if `T` is standard smooth of relative dimension `m` over `S`, there is an étale map
  `D = MvPolynomial (Fin m) S → T` (`Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`), and
  the map factors as `T ⊗[S] H1(L_{S/R}) → T ⊗[D] H1(L_{D/R}) → H1(L_{T/R})`; the first map is injective by
  `poly_step` and flatness of `T` over `D`, the second by the ported
  `Algebra.H1Cotangent.liftBaseChange_map_injective_of_etale`.
- `main`: a smooth algebra is Zariski-locally standard smooth (`RingHom.smooth_iff_locally_isStandardSmooth`);
  an element of the kernel vanishes after each localisation `T_r` by `chart_step` and naturality of `H1`, hence
  vanishes (`Module.eq_zero_of_isLocalized_span`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- noncomputable def `P2MW.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_smooth.JZInj.algPoly`
- scoped instance `P2MW.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_smooth.JZInj.isScalarTower_poly`
- noncomputable def `P2MW.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_smooth.JZInj.polyEquiv`
- theorem `P2MW.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_smooth.JZInj.polyEquiv_tmul`
- theorem `P2MW.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_smooth.JZInj.poly_step`
- theorem `P2MW.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_smooth.JZInj.chart_step`
- theorem `P2MW.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_smooth.JZInj.main`
- theorem `P2MW.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_smooth.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_Algebra_H1Cotangent_liftBaseChange_map_injective_of_etale` (same contribution).
Other imports: `Mathlib`.
