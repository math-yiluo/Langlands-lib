# `Langlands.AnthropicFLT.P2M.Sol.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem`. Statement. `Finsupp.card_le_macaulayPow_card_of_forall_sub_single_mem` (Macaulay's bound, combinatorial form): let `d ≥ 1`,
`B` a finite set of monomials in `n + 1` variables of degree `d` and `C` a finite set of monomials of degree `d + 1`
such that for every `u ∈ C` and every variable `i` occurring in `u`, `u / xᵢ ∈ B`. Then
`|C| ≤ Nat.macaulayPow d |B|` (the `d`-th Macaulay power of `|B|`).

Proof (compression). Section `Tower`: arithmetic of Macaulay representations (`top`, `rem`, `low`, monotonicity of
`macaulayPow`, `macaulayPow_add_le`, `tower_bound`). Section `Compression`: for a set `X` of monomials, the largest
possible `C` is `Bplus X` (monomials of degree `e + 1` all of whose divisions lie in `X`), restricted to monomials in
the first `w` variables (`MonW`). Compressing `X` along a pair of variables (`comp`, moving exponent from one
variable to another) keeps `|X|` and does not decrease `|Bplus X|` (`card_comp`, `card_Bplus_le_comp`); iterating
with a decreasing potential (`pot`) reaches a stable set (`exists_stable`). For stable sets, `X` is sliced by the
exponent of the last variable (`T`), and the slices satisfy the hypotheses of `tower_bound`, which gives
`|Bplus X| ≤ macaulayPow e |X|` by induction on the number of variables (`stable_bound`, `main`). Applying this to
`X = B` gives the claim, since `C ⊆ Bplus B`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.top`
- def `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.rem`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.macaulayPow_zero`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.macaulayPow_succ`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.sub_le_choose`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.choose_top_le`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.lt_choose_of_top_lt`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.lt_choose_top_succ`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.top_eq_of`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.le_top_of_choose_le`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.top_lt_of_lt_choose`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.d_le_top`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.top_zero_right`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.d_lt_top_of_pos`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.top_zero_left`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.rem_zero_left`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.rem_zero_right`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.rem_add_choose`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.rem_lt`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.macaulayPow_lt_choose`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.macaulayPow_mono`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.macaulayPow_one`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.macaulayPow_zero_right`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.top_succ_of_le`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.macaulayPow_eq_self`
- def `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.low`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.low_zero`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.low_succ`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.low_zero_right`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.low_eq_zero`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.low_lt_choose`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.macaulayPow_low_add`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.le_choose_add_low`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.le_add_low`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.macaulayPow_add_le`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.tower_bound`
- def `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.Mon`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.mem_Mon`
- def `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.MonW`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.mem_MonW`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.MonW_zero_succ`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.MonW_zero_right`
- def `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.Bplus`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.mem_Bplus`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.Bplus_subset_MonW`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.degree_sub_single`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.exists_one_le_of_degree_ne_zero`
- def `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.mv`
- def `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.key`
- def `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.J`
- def `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.comp`
- def `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.wt`
- def `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.pot`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.mv_apply`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.mv_apply_i`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.mem_J`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.card_J_le`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.J_mono`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.mv_injective`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.mv_apply_c`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.mv_apply_ne`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.key_apply_i`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.key_apply_c`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.key_apply_ne`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.ext3`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.mv_key`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.key_mv`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.key_key`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.mv_self`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.sub_add_eq_mv`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.mv_sub_single_i`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.mv_sub_single_i'`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.mv_sub_single_c`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.mv_sub_single_ne`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.mem_comp_iff`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.comp_mono`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.comp_step_mem`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.sum_biUnion_mv`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.key_of_mem_image`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.sum_eq_sum_key`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.sum_comp`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.card_comp`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.degree_mv`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.mv_mem_MonW`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.comp_subset_MonW`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.sum_range_card_le`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.min_card_le`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.sub_single_mem_comp`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.card_Bplus_le_comp`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.wt_mv`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.pot_comp_lt`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.exists_stable`
- def `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.T`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.T_subset`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.mem_T_iff`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.card_T`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.sum_card_T`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.card_Bplus_succ_le`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.sub_add_single_comm`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.T_subset_Bplus`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.card_T_last_le`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.card_T_last_eq`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.stable_bound`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.MacaulayCL.main`
- theorem `P2MW.S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Nat_MacaulayPow` (same contribution).
Other imports: `Mathlib`.
