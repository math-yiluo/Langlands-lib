# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq`

Ported module of the proof submitted by task `e36ae7da-512e-4a4d-a902-71146c92ec82` (descent of properness to finitely generated subalgebras). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq.solution` applied to the explicit arguments of the theorem. The theorem statement is unchanged.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

States: for a commutative ring `R`, `n : ℕ`, `i : Fin (n + 1)`, an `R`-algebra `B` and
`b : Fin (n + 1) → B` with `b i = 1`, there is an `R`-algebra map `φ` from the degree-zero part of the
localisation of `MvPolynomial (Fin (n + 1)) R` at `X i` (`HomogeneousLocalization.Away` for the grading by
homogeneous polynomials; the affine chart `D₊(X i)` of projective space) to `B` with
`φ (ProjSpace.ratio R n i k) = b k` for all `k`, where `ProjSpace.ratio R n i k` is `X k / X i` (defined in
the ported module `Definitions.Def_AlgebraicGeometry_ProjSpace`). The proof term applies the companion
solution theorem.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `AlgebraicGeometry.ProjSpace.exists_algHom_away_apply_ratio_eq`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (published with the FLT port of task `69435287-9f1e-4abd-8483-5e65ff23668a`), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq` (ported by this task).
All modules also import `Mathlib`.
