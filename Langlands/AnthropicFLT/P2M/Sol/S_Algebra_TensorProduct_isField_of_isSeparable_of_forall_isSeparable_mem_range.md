# `Langlands.AnthropicFLT.P2M.Sol.S_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isSeparable_mem_range`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isSeparable_mem_range.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isSeparable_mem_range.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isSeparable_mem_range`. Statement. `Algebra.TensorProduct.isField_of_isSeparable_of_forall_isSeparable_mem_range`: let `F` and `K` be
field extensions of `k` with `K / k` separable, and suppose `k` is separably closed in `F` (every
element of `F` separable over `k` lies in `k`). Then `F ⊗[k] K` is a field.

Proof (namespace `P2mSepClosedTensorField`). By Mathlib's
`IntermediateField.LinearDisjoint.isField_of_forall` it suffices that for all embeddings `fa : F → Ω`,
`fb : K → Ω` into a common field the images are linearly disjoint over `k`
(`linearDisjoint_range`). For this, `natDegree_minpoly_eq`: an element `β` separable over `k` has
the same minimal polynomial degree over `F` as over `k` (the coefficients of its minimal polynomial
over `F` are separable over `k`, hence in `k`); hence `F` and `k[x]` are linearly disjoint for
separable `x` (`linearDisjoint_adjoin_singleton`). Every finite-dimensional subalgebra of the image
of `K` lies in some `k[fb β]` (primitive element theorem, `exists_le_adjoin_singleton`), and linear
disjointness is checked on finite-dimensional subalgebras.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isSeparable_mem_range.P2mSepClosedTensorField.natDegree_minpoly_eq`
- theorem `P2MW.S_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isSeparable_mem_range.P2mSepClosedTensorField.hsc_range`
- theorem `P2MW.S_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isSeparable_mem_range.P2mSepClosedTensorField.linearDisjoint_adjoin_singleton`
- theorem `P2MW.S_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isSeparable_mem_range.P2mSepClosedTensorField.exists_le_adjoin_singleton`
- theorem `P2MW.S_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isSeparable_mem_range.P2mSepClosedTensorField.linearDisjoint_range`
- theorem `P2MW.S_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isSeparable_mem_range.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
