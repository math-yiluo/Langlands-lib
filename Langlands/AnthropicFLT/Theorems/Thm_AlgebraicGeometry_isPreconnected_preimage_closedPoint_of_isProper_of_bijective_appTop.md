# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop`

Ported for task `ab019f66-cba5-4921-aa53-b9cfb52e5456` (descent of geometric connectedness to finitely generated subalgebras). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop.solution q hq`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged.
- No other change: the declarations, statements and proofs are the FLT text. The FLT `attribute [-…]`
  lines after the imports (which locally deactivate instances or simp lemmas declared in imported FLT
  modules) are kept unchanged.

## Content

The closed fibre is connected (Zariski's connectedness over a local base): for a noetherian local
ring `A` and a proper morphism `q : P ⟶ Spec A` with `q.appTop` bijective, the preimage
`q ⁻¹' {closedPoint A}` of the closed point is a preconnected subset of `P`. The proof term applies
the companion solution theorem.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `AlgebraicGeometry.isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_isPreconnected_preimage_closedPoint_of_isProper_of_bijective_appTop` (same contribution).
All modules also import `Mathlib`.
