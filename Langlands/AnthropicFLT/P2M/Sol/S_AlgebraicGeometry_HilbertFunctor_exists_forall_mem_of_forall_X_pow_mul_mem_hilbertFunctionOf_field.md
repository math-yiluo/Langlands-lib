# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_HilbertFunctor_exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf_field`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_HilbertFunctor_exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf_field.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 23 here); in 8 lines the replacements `Type` (universe 0) → `Type uz` (8 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf_field.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf_field`. Statement. `AlgebraicGeometry.HilbertFunctor.exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf_field`:
the field case of the saturation statement: there is `D₀` such that for every `m ≥ D₀`, every field
`K` (universe `uz`), every point `p` over `K` with Hilbert function `hilbertFunctionOf n P m` and
every form `F` of degree `d ≥ m` with `Xᵢ^N F ∈ p.I` for all `i` (some `N`), `F ∈ p.I`.

Proof (namespace `SatHighField`). The function `H(e) = ⌊P(e)⌋` satisfies `H(e + 1) ≤ macaulayPow e (H e)`
for large `e` (ported `MvPolynomial.exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval`
and `MvPolynomial.finrank_piece_succ_le_macaulayPow`), hence equality from some `D₁` on (ported
`Nat.exists_forall_eq_macaulayPow_of_forall_le_macaulayPow`). For `m` beyond all bounds, ideals of
points are generated in degree `m` (`Point.I_eq_span_of_forall_finrank_piece_succ_le`) and have maximal
growth from `m` to `m + 1`. Lemma `core` (over an infinite field): with maximal growth, the ported
`MvPolynomial.exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow`
gives a nonzero form `G` such that `ℓ F ∈ I` implies `F ∈ I` for linear forms `ℓ` with `G(ℓ) ≠ 0`;
since every form of degree `(n + 1)N` times `F` lies in `I` (`mul_mem_of_forall_X_pow_mul_mem`), the
factors can be peeled off. For a general field pass to the algebraic closure, extend the point
(`exists_point_I_eq_map`) and descend membership through the base change of pieces.

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf_field.SatHighField.homogeneous_of_span`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf_field.SatHighField.finrank_piece_eq`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf_field.SatHighField.mul_mem_of_forall_X_pow_mul_mem`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf_field.SatHighField.core`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_forall_mem_of_forall_X_pow_mul_mem_hilbertFunctionOf_field.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_Nat_MacaulayPow` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_Point_I_eq_span_of_forall_finrank_piece_succ_le` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_exists_forall_finrank_piece_succ_le_eval_and_exists_eq_eval` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_finrank_piece_succ_le_macaulayPow` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_exists_forall_eval_ne_zero_mem_of_mul_mem_of_finrank_piece_succ_eq_macaulayPow` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_point_I_eq_map` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_linearEquiv_baseChange_piece_map` (same contribution).
Other imports: none.
