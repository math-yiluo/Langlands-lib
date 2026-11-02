# `Langlands.AnthropicFLT.P2M.Sol.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- Manual edit for Mathlib drift (FLT line 309, line 320 here): `Pi.Lex.wellFounded (· < ·) (fun _ => wellFounded_lt)` is replaced by `Pi.Lex.wellFounded (· < ·) (hs := fun _ => wellFounded_lt)`. In the project's Mathlib the well-foundedness hypothesis `hs` of `Pi.Lex.wellFounded` (Mathlib `Data/DFinsupp/WellFounded.lean`) is an instance-implicit argument instead of an explicit one, so it is passed by name.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow`. Statement. `Nat.exists_forall_eq_macaulayPow_of_forall_le_macaulayPow` (stabilization of Macaulay representations): if
`H(d + 1) ≤ H(d)^⟨d⟩` for all `d ≥ d₀ ≥ 1`, then `H(e + 1) = H(e)^⟨e⟩` for all large `e`.

Proof. Encode the `d`-th Macaulay representation of `H(d)` as a vector of "shifted" binomial parameters (`vec`,
`vec_macaulayPow`, `top_macaulayPow`, `rem_macaulayPow`). The inequality `H(d + 1) ≤ H(d)^⟨d⟩` means that the vector for
`d + 1` is lexicographically at most the vector for `d` (`eq_or_lex_of_le`, `vec_succ_le`), and the vectors take values
in a set where the lexicographic order is well founded with bounded length (`vec_antitone`, `vec_injective`,
`head_le_of_eq_or_lex`, `cnt`, `cv_lex`). A non-increasing sequence there is eventually constant, and constancy of
the vector is equality `H(e + 1) = H(e)^⟨e⟩` (`eventually_eq`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.top`
- def `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.rem`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.macaulayPow_zero`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.macaulayPow_succ`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.sub_le_choose`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.choose_top_le`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.top_le`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.lt_choose_of_top_lt`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.lt_choose_top_succ`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.top_eq_of`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.le_top_of_choose_le`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.top_lt_of_lt_choose`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.d_le_top`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.top_zero_right`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.d_lt_top_of_pos`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.top_zero_left`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.rem_zero_left`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.rem_add_choose`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.rem_lt`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.top_mono`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.macaulayPow_lt_choose`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.top_macaulayPow`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.rem_macaulayPow`
- def `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.vec`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.vec_zero`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.vec_succ_zero`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.vec_succ_succ`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.vec_macaulayPow`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.vec_eq_zero_of_le`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.vec_succ_le`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.vec_antitone`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.lex_vec_of_lt`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.not_lex_self`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.vec_injective`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.eq_or_lex_of_le`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.head_le_of_eq_or_lex`
- def `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.cnt`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.cnt_eq`
- def `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.cv`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.cv_lex`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.GotzNum.eventually_eq`
- theorem `P2MW.S_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Nat_MacaulayPow` (same contribution).
Other imports: `Mathlib`.
