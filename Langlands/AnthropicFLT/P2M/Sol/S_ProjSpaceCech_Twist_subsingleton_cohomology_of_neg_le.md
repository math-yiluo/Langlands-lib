# `Langlands.AnthropicFLT.P2M.Sol.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept.
- 44 `p2m_open_scoped "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that activates the scoped extensions of the named namespaces without opening them) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces; a trailing ` in` is kept.
- 2 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- Manual edit for Mathlib drift (FLT line 217, line 228 here): `Finsupp.mapDomain_apply (Twist.Mon.incl_injective n d _)` is replaced by `Finsupp.mapDomain_apply_of_injective (Twist.Mon.incl_injective n d _)`. In the project's Mathlib the lemma `Finsupp.mapDomain_apply` for injective maps is named `Finsupp.mapDomain_apply_of_injective` (Mathlib `Data/Finsupp/Basic.lean`), with the same statement.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le`. Statement. `ProjSpaceCech.Twist.subsingleton_cohomology_of_neg_le`: `Hⁱ(ℙⁿ_R, 𝒪(d))` vanishes for `i ≥ 1` and `d ≥ -n` (Čech
cohomology of the twisting sheaves).

Proof. For `1 ≤ i ≤ n - 1` this is the ported `ProjSpaceCech.Twist.subsingleton_cohomology_succ_of_le`, and for `i > n` the
ported `ProjSpaceCech.Twist.subsingleton_cohomology_of_lt`. The top degree `i = n` is handled directly (section `HN`,
`NegLe`): `Hⁿ` is spanned by the classes of monomials with all exponents negative (`sfull`, `eq_sfull`,
`basis_mem_range`), and there are none in degree `d ≥ -n` (`subsingleton_cohomology_top_of_neg_le`); the homotopy
machinery of sections `Homotopy`–`Homot` is shared with the ported lemma.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.Twist.idx_canonical`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.Twist.idx_eq_of_img`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.Twist.img_face`
- def `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.Twist.altOfFinset`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.Twist.img_altOfFinset`
- def `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.Twist.altPos`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.Twist.idx_val_altPos`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.Twist.altPos_val`
- def `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.Twist.altInsert`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.Twist.img_altInsert`
- def `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.Twist.insPos`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.Twist.altInsert_val_insPos`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.Twist.face_altInsert_insPos`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.Twist.img_face_altInsert_ne`
- def `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.Twist.coeff`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.Twist.coeff_eq`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.Twist.coeff_of_not`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.Twist.coeff_add`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.Twist.coeff_smul`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.Twist.ext_coeff`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.Twist.coeff_d`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.Twist.coeff_piSingle`
- def `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.Twist.posMin`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.Twist.posMin_notMem_negSupp`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.altPos_eq_card`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.insPos_eq_card`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.img_subset_altInsert`
- def `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.hj`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.hj_apply_of_mem`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.coeff_hj_of_mem`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.coeff_hj`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.coeff_zero`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.dh_hd_coeff`
- def `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.coeffL`
- def `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.homot`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.homot_basis`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.coeff_homot`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.subsingleton_cohomology_succ_of_le'`
- def `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.sfull`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.img_sfull`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.eq_sfull`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.basis_mem_range`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.subsingleton_cohomology_top_of_neg_le`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.Twist.subsingleton_cohomology_of_neg_le'`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_of_neg_le.ProjSpaceCech.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist` (Library), `Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_Twist_subsingleton_cohomology_of_lt` (same contribution).
Other imports: `Mathlib`.
