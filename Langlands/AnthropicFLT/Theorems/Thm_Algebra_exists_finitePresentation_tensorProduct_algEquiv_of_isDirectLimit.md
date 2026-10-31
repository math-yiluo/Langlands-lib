# `Langlands.AnthropicFLT.Theorems.Thm_Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit`

Ported module of the proof submitted by task `80ab0ad1-6602-4bc6-8c52-3f88f45f4c83` (descent of schemes of finite presentation along finitely generated subalgebras). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit.solution` applied to the explicit arguments of the theorem. The theorem statement is unchanged.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

States: let `R` be the direct limit (`IsDirectLimit`) of a directed system of commutative rings `G i`
over a nonempty directed index type, and let `A` be a finitely presented `R`-algebra. Then for some
index `i` there are a finitely presented `G i`-algebra `A₀` and an `R`-algebra isomorphism
`R ⊗[G i] A₀ ≃ₐ[R] A`. The proof term applies the solution theorem of the companion `P2M.Sol` module
to the explicit arguments.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `Algebra.exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_Algebra_IsDirectLimit`, `Langlands.AnthropicFLT.P2M.Sol.S_Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit`.
All modules also import `Mathlib`.
