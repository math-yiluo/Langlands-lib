# A module squeezed between two finite modules over a noetherian ring is finite

`Langlands.AnthropicFLT.P2M.Sol.S_Module_Finite_of_ker_le_range_of_isNoetherianRing` proves the theorem `P2MW.S_Module_Finite_of_ker_le_range_of_isNoetherianRing.solution`. Its statement is that of `Module.Finite.of_ker_le_range_of_isNoetherianRing`, which `Langlands.AnthropicFLT.Theorems.Thm_Module_Finite_of_ker_le_range_of_isNoetherianRing` states under its FLT name.

## Statement

Let `R` be a noetherian commutative ring, `M`, `N₁`, `N₂` modules over `R` with
`N₁` and `N₂` finite, and `α : N₁ →ₗ[R] M`, `β : M →ₗ[R] N₂` linear maps with
`ker β ≤ range α`. Then `M` is a finite `R`-module. No exactness at `N₁` or
`N₂` is assumed.

## Provenance and licence

The Lean file is ported from `P2M/Sol/S_Module_Finite_of_ker_le_range_of_isNoetherianRing.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed. No declaration, statement or proof step changed;

## Proof outline

The range of `α` is the image of the finite module `N₁`, hence finitely
generated, hence noetherian over the noetherian ring `R`; and `N₂` is
noetherian (`isNoetherian_of_isNoetherianRing_of_finite`). By
`Submodule.fg_of_fg_map_of_fg_inf_ker` applied to `β` and the submodule `⊤`
of `M`, it suffices that `β(M)` and `ker β` are finitely generated. The first
is a submodule of the noetherian module `N₂`. For the second, `ker β` lies in
`range α`, so it is the image under the inclusion of the submodule
`comap (range α).subtype (ker β)` of the noetherian module `range α`; that
submodule is finitely generated, and so is its image.
