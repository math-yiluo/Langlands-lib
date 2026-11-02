# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso_orderDual`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso_orderDual.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso_orderDual.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso_orderDual`. Statement. `AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_of_orderIso_orderDual`: the same invariance when the
index sets are related by an order-reversing isomorphism `e : K.ι ≃o (K'.ι)ᵒᵈ` with
`K'.U (e i) = K.U i`.

Proof (namespace `P2mCechReverse`). Increasing tuples for `K` correspond to increasing tuples for `K'` by
applying `e` and reversing the order (`idx`, with `Fin.rev`); faces correspond with reversed positions
(`idx_face`), introducing the sign `(-1)^j ↦ (-1)^{i+1-j}`. Multiplying the reindexing map in degree `i`
by the sign `sgn i = ∏_{n ≤ i} (-1)^n` (`sgn`, `sgn_mul_self`, `neg_one_pow_rev`) gives bijective cochain
maps commuting with the differentials (`d_phi`), hence the isomorphisms (`main`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso_orderDual.P2mCechReverse.idx`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso_orderDual.P2mCechReverse.idx_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso_orderDual.P2mCechReverse.idx_face`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso_orderDual.P2mCechReverse.inter_idx`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso_orderDual.P2mCechReverse.inter_symm`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso_orderDual.P2mCechReverse.sgn`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso_orderDual.P2mCechReverse.sgn_succ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso_orderDual.P2mCechReverse.sgn_mul_self`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso_orderDual.P2mCechReverse.phi`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso_orderDual.P2mCechReverse.phi_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso_orderDual.P2mCechReverse.res_eq_of_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso_orderDual.P2mCechReverse.phi_apply_idx`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso_orderDual.P2mCechReverse.phi_apply_face`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso_orderDual.P2mCechReverse.inter_face_le`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso_orderDual.P2mCechReverse.phi_surjective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso_orderDual.P2mCechReverse.phi_injective`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso_orderDual.P2mCechReverse.neg_one_pow_rev`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso_orderDual.P2mCechReverse.d_phi`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso_orderDual.P2mCechReverse.main`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_of_orderIso_orderDual.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d` (Library), `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact` (same contribution).
Other imports: `Mathlib`.
