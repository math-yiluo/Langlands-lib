# A module squeezed between two finite modules over a noetherian ring is finite

`Langlands.AnthropicFLT.Theorems.Thm_Module_Finite_of_ker_le_range_of_isNoetherianRing` proves the theorem `Module.Finite.of_ker_le_range_of_isNoetherianRing`.

## Statement

Let `R` be a noetherian commutative ring, `M`, `N₁`, `N₂` modules over `R` with
`N₁` and `N₂` finite, and `α : N₁ →ₗ[R] M`, `β : M →ₗ[R] N₂` linear maps with
`ker β ≤ range α`. Then `M` is a finite `R`-module. No exactness at `N₁` or
`N₂` is assumed.

## Provenance and licence

The Lean file is ported from `Theorems/Thm_Module_Finite_of_ker_le_range_of_isNoetherianRing.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_Module_Finite_of_ker_le_range_of_isNoetherianRing.solution` is written `by exact @_root_.P2MW.S_Module_Finite_of_ker_le_range_of_isNoetherianRing.solution` applied to the theorem's binders in order (`_` for anonymous instance binders). The statement is unchanged;

## Proof

The proof applies `P2MW.S_Module_Finite_of_ker_le_range_of_isNoetherianRing.solution` from `Langlands.AnthropicFLT.P2M.Sol.S_Module_Finite_of_ker_le_range_of_isNoetherianRing`, which has the same statement. The Markdown of that module outlines the argument.
