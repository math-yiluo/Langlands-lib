# `Langlands.AnthropicFLT.P2M.Sol.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept.
- 38 `p2m_open_scoped "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that activates the scoped extensions of the named namespaces without opening them) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces; a trailing ` in` is kept.
- 2 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- Manual edit for Mathlib drift (FLT line 215, line 226 here): `Finsupp.mapDomain_apply (Twist.Mon.incl_injective n d _)` is replaced by `Finsupp.mapDomain_apply_of_injective (Twist.Mon.incl_injective n d _)`. In the project's Mathlib the lemma `Finsupp.mapDomain_apply` for injective maps is named `Finsupp.mapDomain_apply_of_injective` (Mathlib `Data/Finsupp/Basic.lean`), with the same statement.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le`. Statement. `ProjSpaceCech.Twist.subsingleton_cohomology_succ_of_le`: `Hⁱ⁺¹(ℙⁿ_R, 𝒪(d))` vanishes for `i + 2 ≤ n` (intermediate
Čech cohomology of the twists, for all `d`).

Proof. The Čech complex splits as a direct sum over Laurent monomials (`coeff`, `coeff_d`, `ext_coeff`). For a monomial
with set of negative exponents `N` (`posMin`, `posMin_notMem_negSupp`), the summand is the complex of alternating
functions on the subsets containing `N`, and for an index `j` with nonnegative exponent an explicit contracting homotopy
inserts `j` (sections `Homotopy`, `Rank`, `Hj`, `DhHd`, `Homot`: `altInsert`, `insPos`, `hj`, `dh_hd_coeff`, `homot`,
`coeff_homot`); such a `j` exists except in the top degree, so intermediate cohomology vanishes
(`subsingleton_cohomology_succ_of_le'`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.Twist.idx_canonical`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.Twist.idx_eq_of_img`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.Twist.img_face`
- def `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.Twist.altOfFinset`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.Twist.img_altOfFinset`
- def `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.Twist.altPos`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.Twist.idx_val_altPos`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.Twist.altPos_val`
- def `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.Twist.altInsert`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.Twist.img_altInsert`
- def `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.Twist.insPos`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.Twist.altInsert_val_insPos`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.Twist.face_altInsert_insPos`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.Twist.img_face_altInsert_ne`
- def `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.Twist.coeff`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.Twist.coeff_eq`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.Twist.coeff_of_not`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.Twist.coeff_add`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.Twist.coeff_smul`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.Twist.ext_coeff`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.Twist.coeff_d`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.Twist.coeff_piSingle`
- def `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.Twist.posMin`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.Twist.posMin_notMem_negSupp`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.altPos_eq_card`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.insPos_eq_card`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.img_subset_altInsert`
- def `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.hj`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.hj_apply_of_mem`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.coeff_hj_of_mem`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.coeff_hj`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.coeff_zero`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.dh_hd_coeff`
- def `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.coeffL`
- def `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.homot`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.homot_basis`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.coeff_homot`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.Twist.subsingleton_cohomology_succ_of_le'`
- theorem `P2MW.S_ProjSpaceCech_Twist_subsingleton_cohomology_succ_of_le.ProjSpaceCech.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist` (Library).
Other imports: `Mathlib`.
