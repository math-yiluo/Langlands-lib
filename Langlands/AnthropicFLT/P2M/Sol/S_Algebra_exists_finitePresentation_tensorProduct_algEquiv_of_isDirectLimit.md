# `Langlands.AnthropicFLT.P2M.Sol.S_Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit`

Ported module of the proof submitted by task `80ab0ad1-6602-4bc6-8c52-3f88f45f4c83` (descent of schemes of finite presentation along finitely generated subalgebras). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof of the statement in the companion `Theorems` module. Choose a finite presentation `P` of `A`
over `R` (Mathlib `Algebra.Presentation.ofFinitePresentation`). Its finitely many coefficients lie in the
image of a single `G i`, since every element of `R` comes from some stage and the index set is directed
(`AlgSpreadDirected.exists_subset_range_of_finite`, using `range_mono`). Then Mathlib's
`Algebra.Presentation.ModelOfHasCoeffs` gives the finitely presented `G i`-algebra `A₀`, and
`tensorModelOfHasCoeffsEquiv` gives the isomorphism `R ⊗[G i] A₀ ≃ₐ[R] A`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit.AlgSpreadDirected.range_mono`
- theorem `P2MW.S_Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit.AlgSpreadDirected.exists_subset_range_of_finite`
- theorem `P2MW.S_Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_Mathlib_Algebra_IsDirectLimit`.
All modules also import `Mathlib`.
