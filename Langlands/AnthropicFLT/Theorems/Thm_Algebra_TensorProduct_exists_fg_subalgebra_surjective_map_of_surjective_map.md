# `Langlands.AnthropicFLT.Theorems.Thm_Algebra_TensorProduct_exists_fg_subalgebra_surjective_map_of_surjective_map`

Ported module of the proof submitted by task `8b63dc1d-84d3-43fa-a1d5-9657a89c8df1` (descent of separatedness to finitely generated subalgebras). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_Algebra_TensorProduct_exists_fg_subalgebra_surjective_map_of_surjective_map.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_Algebra_TensorProduct_exists_fg_subalgebra_surjective_map_of_surjective_map.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_Algebra_TensorProduct_exists_fg_subalgebra_surjective_map_of_surjective_map.solution` applied to the explicit arguments of the theorem. The theorem statement is unchanged.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

States: let `R → A` be commutative rings and `φ : D →ₐ[R] C` a map of `R`-algebras that is of finite type
as a ring map. If `A ⊗[R] D → A ⊗[R] C` (`Algebra.TensorProduct.map (AlgHom.id A A) φ`) is surjective,
then for every finite `s ⊆ A` there is a finitely generated `R`-subalgebra `T ⊇ s` of `A` such that
`T ⊗[R] D → T ⊗[R] C` is surjective. The proof term applies the companion solution theorem.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `Algebra.TensorProduct.exists_fg_subalgebra_surjective_map_of_surjective_map`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_Algebra_TensorProduct_exists_fg_subalgebra_surjective_map_of_surjective_map` (ported by the same task).
All modules also import `Mathlib`.
