# `Langlands.AnthropicFLT.P2M.Sol.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular`

Ported for task `83bb1057-d232-4d4d-8b0b-92eedc47eb0b` (existence of quotients of projectively embedded abelian schemes by finite étale subgroups) by Worker 1224. Proof module (FLT `P2M/Sol/`).

Included without change to the Lean file by Worker 293 in the proof contribution of task `d86a245c-cda3-4bba-b453-e9e7acec04b5` (smoothness descent along a surjective étale map on the source), with Worker 1224 as coauthor; copied from revision 2 of the task-`83bb1057` draft. After review, Worker 293 corrected the description of `phi` and of `main` in the Content section of this Markdown file.

## Source and licence

Port of `P2M/Sol/S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 2 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions) are replaced by standard `open _root_.N₁ _root_.N₂ …` commands with the same namespaces: `Algebra TensorProduct.Algebra TensorProduct Algebra.TensorProduct`; `Algebra TensorProduct.Algebra TensorProduct Algebra.TensorProduct`.
- 1 `p2m_reactivate "N"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N` with the same namespaces, which activates the same scoped extensions: `P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular.P2mKcK1Loc`.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `solution` proves the statement of
`Algebra.injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular` (companion
module `Langlands.AnthropicFLT.Theorems.Thm_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular`).

Proof (namespace `P2mKcK1Loc`).
- Section `Alt`: alternating matrices (`IsAlt`), and `exists_isAlt_of_sum_smul_eq_zero`: for a weakly regular
  sequence `r` on a module, every relation `∑ r_j m_j = 0` is a Koszul combination `m_j = ∑_l r_l d_{jl}` with
  `d` alternating (induction on the length of the sequence).
- Section `SyzLoc`: `HasKoszulSyzygies r` says every relation among the `r_j` is a Koszul combination.
  `hasKoszulSyzygies_of_forall_isWeaklyRegular`: if the sequence is weakly regular in the localisation at every
  maximal ideal containing it, it has Koszul syzygies. For a relation `c`, the ideal `goodIdeal r c` of `u`
  with `u·c` a Koszul combination contains every `r_l` and, by the local statement and clearing
  denominators (`exists_isAlt_integer`), is not contained in any maximal ideal containing the `r_j`; so it is
  the unit ideal. `hasKoszulSyzygies_get_of_forall_isWeaklyRegular` restates this for a list.
- Section `Functorial`: `map_map` is the functoriality of `H1Cotangent.map` along `S → T → T'`.
  `phi S T T' M : T ⊗[S] M →ₗ[T] T' ⊗[S] M` is the `T`-linear map sending `t ⊗ m` to
  `algebraMap T T' t ⊗ m` (`phi_tmul`). `isBaseChange_phi` says that `phi` is a base change along
  `T → T'`: its `T'`-linear extension `T' ⊗[T] (T ⊗[S] M) → T' ⊗[S] M` is an isomorphism. Hence for
  `T' = T_g` the map `phi` itself is a localisation map at the powers of `g` (`isLocalizedModule_phi`).
  `square`: for `x ∈ T ⊗[S] H1(S/R)`, the map `H1(T/R) → H1(T'/R)` sends
  `(H1Cotangent.map R R S T).liftBaseChange T x` to `(H1Cotangent.map R R S T').liftBaseChange T' (phi x)`.
- Section `Main`: `chart` treats one chart by the ported
  `Algebra.injective_liftBaseChange_h1CotangentMap_of_ker_eq_span_range_of_forall_exists_alternating`;
  `main` shows that an element `x` of the kernel is zero by `Module.eq_zero_of_isLocalized_span`, using the
  localisation maps `phi` to `T_g ⊗[S] H1(S/R)`, `g ∈ s`: by `square`, `phi x` lies in the kernel of the map
  over `T_g`, which is injective by `chart`, so `phi x = 0`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular.P2mKcK1Loc.IsAlt`
- theorem `P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular.P2mKcK1Loc.sum_sum_smul_eq_zero_of_isAlt`
- theorem `P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular.P2mKcK1Loc.exists_isAlt_lift`
- theorem `P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular.P2mKcK1Loc.exists_eq_smul_of_mem_smul_top`
- theorem `P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular.P2mKcK1Loc.exists_isAlt_of_sum_smul_eq_zero`
- def `P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular.P2mKcK1Loc.HasKoszulSyzygies`
- def `P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular.P2mKcK1Loc.goodIdeal`
- lemma `P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular.P2mKcK1Loc.mem_goodIdeal_iff`
- lemma `P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular.P2mKcK1Loc.self_mem_goodIdeal`
- lemma `P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular.P2mKcK1Loc.exists_isAlt_integer`
- theorem `P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular.P2mKcK1Loc.hasKoszulSyzygies_of_forall_isWeaklyRegular`
- theorem `P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular.P2mKcK1Loc.hasKoszulSyzygies_get_of_forall_isWeaklyRegular`
- lemma `P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular.P2mKcK1Loc.map_map`
- noncomputable def `P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular.P2mKcK1Loc.phi`
- lemma `P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular.P2mKcK1Loc.phi_tmul`
- lemma `P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular.P2mKcK1Loc.square`
- lemma `P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular.P2mKcK1Loc.isBaseChange_phi`
- scoped instance `P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular.P2mKcK1Loc.isLocalizedModule_phi`
- theorem `P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular.P2mKcK1Loc.chart`
- theorem `P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular.P2mKcK1Loc.main`
- theorem `P2MW.S_Algebra_injective_liftBaseChange_h1CotangentMap_of_span_eq_top_of_forall_exists_isWeaklyRegular.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_Algebra_injective_liftBaseChange_h1CotangentMap_of_ker_eq_span_range_of_forall_exists_alternating` (same contribution).
Other imports: `Mathlib`.
