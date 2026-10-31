# `Langlands.AnthropicFLT.Theorems.Thm_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite`

Ported for task `ab019f66-cba5-4921-aa53-b9cfb52e5456` (descent of geometric connectedness to finitely generated subalgebras). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite.solution (K := K) B`: the solution theorem applied to the explicit argument `B` and, by name, to the implicit argument `K`. The solution theorem has the same binders as the theorem; `K` occurs only in instance arguments (`IsFractionRing A K`, `IsScalarTower A K L`, `Module.Finite K L`) and not in the conclusion, so it cannot be inferred by unification and is passed by name (manual edit). The theorem statement is unchanged.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Krull–Akizuki theorem with a finite-length addendum: let `A` be a noetherian domain of Krull
dimension at most one (`Ring.KrullDimLE 1 A`) with fraction field `K`, and `L` a finite field
extension of `K` (with compatible `A`-algebra structure). Then every `A`-subalgebra `B` of `L` is
noetherian, has dimension at most one (`Ring.DimensionLEOne B`), and for every nonzero ideal `J` of `B`
the `A`-module `B ⧸ J` has finite length. The proof term applies the companion solution theorem.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `Subalgebra.isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_Subalgebra_isNoetherianRing_and_dimensionLEOne_of_isFractionRing_of_finite` (same contribution).
All modules also import `Mathlib`.
