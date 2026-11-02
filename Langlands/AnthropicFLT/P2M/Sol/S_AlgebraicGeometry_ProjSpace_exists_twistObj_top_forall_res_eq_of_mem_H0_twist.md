# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_twistObj_top_forall_res_eq_of_mem_H0_twist`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_twistObj_top_forall_res_eq_of_mem_H0_twist.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_twistObj_top_forall_res_eq_of_mem_H0_twist.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_twistObj_top_forall_res_eq_of_mem_H0_twist`. Statement. `AlgebraicGeometry.ProjSpace.exists_twistObj_top_forall_res_eq_of_mem_H0_twist`: for an affine
morphism `φ : Z ⟶ ℙⁿ_A`, every Čech `H⁰` class of the twist `φ^* 𝒪(m)` for the pulled-back standard
cover is the family of restrictions of a global section of the twist.

Proof. The degree-`0` index tuples are single charts (`single`, `eq_single`, `inter_single`), and the
cocycle condition on pairs (`pair`, faces `face_pair_zero`, `face_pair_one`,
`inter_single_inf_le_inter_pair`) says that the chart sections agree on overlaps. A compatible family
of twist sections on the charts defines a global twist section componentwise (each component on the
whole chart), whose restrictions are the given ones.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_twistObj_top_forall_res_eq_of_mem_H0_twist.P2mWs6Glue.single`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_twistObj_top_forall_res_eq_of_mem_H0_twist.P2mWs6Glue.eq_single`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_twistObj_top_forall_res_eq_of_mem_H0_twist.P2mWs6Glue.inter_single`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_twistObj_top_forall_res_eq_of_mem_H0_twist.P2mWs6Glue.pair`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_twistObj_top_forall_res_eq_of_mem_H0_twist.P2mWs6Glue.face_pair_zero`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_twistObj_top_forall_res_eq_of_mem_H0_twist.P2mWs6Glue.face_pair_one`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_twistObj_top_forall_res_eq_of_mem_H0_twist.P2mWs6Glue.inter_single_inf_le_inter_pair`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_twistObj_top_forall_res_eq_of_mem_H0_twist.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCover` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (same contribution).
Other imports: `Mathlib`.
