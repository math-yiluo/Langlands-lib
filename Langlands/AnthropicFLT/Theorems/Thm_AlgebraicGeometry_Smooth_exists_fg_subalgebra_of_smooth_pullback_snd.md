# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_exists_fg_subalgebra_of_smooth_pullback_snd`

Ported for task `8836e68b-90ba-4f01-a129-026ad9adfa9d` (descent of smoothness to finitely generated subalgebras). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_Smooth_exists_fg_subalgebra_of_smooth_pullback_snd.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Smooth_exists_fg_subalgebra_of_smooth_pullback_snd.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_Smooth_exists_fg_subalgebra_of_smooth_pullback_snd.solution` applied to the explicit arguments of the theorem. The theorem statement is unchanged.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

States descent of smoothness: for commutative rings `A₀ → A` in `Type u`, a quasi-compact morphism
`f : X ⟶ Spec A₀` that is locally of finite presentation and whose base change
`pullback.snd f (Spec A ⟶ Spec A₀)` is smooth, and a finite set `s ⊆ A`, there is a finitely generated
`A₀`-subalgebra `T ⊇ s` of `A` such that the base change of `f` to `Spec T` is smooth. This is the
statement of `Langlands.AlgebraicGeometry.NoetherianApproximation.SmoothSubalgebraDescentStatement`, the
target of task 8836e68b. The proof term applies the companion solution theorem.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `AlgebraicGeometry.Smooth.exists_fg_subalgebra_of_smooth_pullback_snd`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Smooth_exists_fg_subalgebra_of_smooth_pullback_snd` (same contribution).
All modules also import `Mathlib`.
