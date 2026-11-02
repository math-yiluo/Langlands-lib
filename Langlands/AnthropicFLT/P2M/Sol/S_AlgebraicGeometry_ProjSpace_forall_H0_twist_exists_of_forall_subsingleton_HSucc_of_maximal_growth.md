# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 25 here); in 3 lines the replacements `Type` (universe 0) → `Type uz` (2 places), `Scheme.{0}` → `Scheme.{uz}` (2 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth`. Statement. `AlgebraicGeometry.ProjSpace.forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth`: let
`J` be an ideal over a field generated in degree `m ≥ 1` with maximal growth from `m` to `m + 1`, and
`Z_k ⊆ ℙⁿ_k` a closed subscheme whose forms of degree `≥ m` are those of `J`. If the higher Čech
cohomology of `𝒪_{Z_k}(d)` vanishes for all `d ≥ m`, then for all `d ≥ m` every `H⁰` class of `𝒪_{Z_k}(d)`
is given by a form of degree `d`.

Proof. Combinatorics of Macaulay's function (`top`, `macaulayPow_succ`, `sub_le_choose`,
`lt_choose_of_top_lt`, `one_le_macaulayPow`). The dehomogenization map `Θ` from forms of degree `d` to
`H⁰` (`exists_theta`) has kernel the forms of `J` (`theta_eq_zero_iff`), so `dim piece J d ≤ dim H⁰`. Maximal
growth propagates (ported `MvPolynomial.forall_finrank_piece_succ_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow`),
so `dim piece J d` is eventually a polynomial (ported `Nat.exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow`);
by vanishing of higher cohomology `dim H⁰` is a polynomial of degree `≤ n` (ported
`ProjSpace.exists_polynomial_natDegree_le_forall_finrank_H0_twist_eq_of_forall_subsingleton_HSucc`), and
for large `d` all `H⁰` classes come from forms (ported
`ProjSpace.exists_forall_H0_twist_exists_isHomogeneous_forall_val_eq_of_isClosedImmersion`). Comparing the
two polynomials gives equality of dimensions for all `d ≥ m`, so `Θ` is surjective; the degenerate case
`dim piece J m = 0` is the ported
`ProjSpace.forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_finrank_piece_eq_zero`.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth.RM4Sol.top`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth.RM4Sol.macaulayPow_succ`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth.RM4Sol.sub_le_choose`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth.RM4Sol.lt_choose_of_top_lt`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth.RM4Sol.le_top_of_choose_le`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth.RM4Sol.d_lt_top_of_pos`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth.RM4Sol.one_le_macaulayPow`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth.RM4Sol.chartVal`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth.RM4Sol.isHomogeneous_of_mem`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth.RM4Sol.vertex`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth.RM4Sol.chart_le_inter_vertex`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth.RM4Sol.exists_theta`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth.RM4Sol.theta_eq_zero_iff`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_Nat_MacaulayPow` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearMap_homogeneousSubmodule_twistObj_top_val_eq` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_polynomial_natDegree_le_forall_finrank_H0_twist_eq_of_forall_subsingleton_HSucc` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_forall_H0_twist_exists_isHomogeneous_forall_val_eq_of_isClosedImmersion` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_finrank_piece_eq_zero` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_forall_finrank_piece_succ_eq_macaulayPow_of_finrank_piece_succ_eq_macaulayPow` (same contribution).
Other imports: `Mathlib`.
