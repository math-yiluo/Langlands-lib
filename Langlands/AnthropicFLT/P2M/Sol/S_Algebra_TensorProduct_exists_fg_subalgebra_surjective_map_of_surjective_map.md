# `Langlands.AnthropicFLT.P2M.Sol.S_Algebra_TensorProduct_exists_fg_subalgebra_surjective_map_of_surjective_map`

Ported module of the proof submitted by task `8b63dc1d-84d3-43fa-a1d5-9657a89c8df1` (descent of separatedness to finitely generated subalgebras). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Algebra_TensorProduct_exists_fg_subalgebra_surjective_map_of_surjective_map.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof. One element (`SurjDescGC3.step`): for `c : C`, `1 ⊗ c` has a preimage `w` in `A ⊗[R] D`; `w` comes
from `T₁ ⊗[R] D` for a finitely generated `T₁` (Mathlib `TensorProduct.Algebra.exists_of_fg`), and the
equation `map w = 1 ⊗ c`, which holds in `A ⊗[R] C`, already holds over a larger finitely generated
subalgebra (Mathlib `TensorProduct.Algebra.eq_of_fg_of_subtype_eq`). By induction over a finite list of
generators of `C` as a `D`-algebra, one finitely generated `T ⊇ s` makes all `1 ⊗ cₖ` lie in the range.
The range of the algebra map `T ⊗[R] D → T ⊗[R] C` then contains `1 ⊗ c` for every `c` (induction over
`Algebra.adjoin`) and hence every element `t ⊗ c = (t ⊗ 1)(1 ⊗ c)`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_Algebra_TensorProduct_exists_fg_subalgebra_surjective_map_of_surjective_map.SurjDescGC3.rTensor_comp_map`
- theorem `P2MW.S_Algebra_TensorProduct_exists_fg_subalgebra_surjective_map_of_surjective_map.SurjDescGC3.rTensor_incl_map`
- theorem `P2MW.S_Algebra_TensorProduct_exists_fg_subalgebra_surjective_map_of_surjective_map.SurjDescGC3.step`
- theorem `P2MW.S_Algebra_TensorProduct_exists_fg_subalgebra_surjective_map_of_surjective_map.solution`

## Dependencies

Ported FLT modules imported: none.
All modules also import `Mathlib`.
