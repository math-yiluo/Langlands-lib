# `Langlands.AnthropicFLT.Theorems.Thm_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit`

Ported for task `8836e68b-90ba-4f01-a129-026ad9adfa9d` (descent of smoothness to finitely generated subalgebras). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit.solution` applied to the explicit arguments of the theorem. The theorem statement is unchanged.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Setting: `R` is the direct limit (`IsDirectLimit`) of a directed system of commutative `R₀`-algebras `G i` (nonempty directed index type, transition `R₀`-algebra maps `f i j h`), with `R₀`-algebra structures `G i → R` forming scalar towers. States: for an `R₀`-algebra `A` of finite type, any `R₀`-algebra `B` and two `G i`-algebra maps
`φ₁ φ₂ : G i ⊗[R₀] A →ₐ[G i] G i ⊗[R₀] B` that agree after composing with `G i ⊗[R₀] B → R ⊗[R₀] B`,
there is `j ≥ i` such that they agree after composing with `G i ⊗[R₀] B → G j ⊗[R₀] B`. The proof term
applies the companion solution theorem.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `Algebra.exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_Algebra_IsDirectLimit` (Library, ported by task `80ab0ad1-6602-4bc6-8c52-3f88f45f4c83`), `Langlands.AnthropicFLT.P2M.Sol.S_Algebra_exists_tensorProduct_map_apply_eq_of_finiteType_of_isDirectLimit` (same contribution).
All modules also import `Mathlib`.
