# A bounded flat complex with finite cohomology has a two-term free model for H⁰ universally

`Langlands.AnthropicFLT.Theorems.Thm_Module_exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex` proves the theorem `Module.exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex`.

## Statement

Let `R` be a noetherian commutative ring and
`C^0 → C^1 → C^2 → …` a cochain complex of flat `R`-modules (`d_{i+1} ∘ d_i = 0`)
that vanishes above some degree `n` (each `C^i` with `i > n` is a
subsingleton). Suppose `ker d_0` is a finite `R`-module and every cohomology
module `ker d_{i+1} / im d_i` is finite. Then there are a two-term complex `G`
(the FLT structure `CoherentBaseChange.TwoTermComplex`: a linear map
`d : C0 → C1` of finite free `R`-modules) and linear maps `ι0 : C0 → C^0`,
`ι1 : C1 → C^1` with `d_0 ∘ ι0 = ι1 ∘ d`, such that for every `R`-algebra `A`
the induced map `ker (A ⊗ d) → ker (A ⊗ d_0)`
(`TwoChartCech.kerMapBaseChange`) is bijective.

## Provenance and licence

The Lean file is ported from `Theorems/Thm_Module_exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_Module_exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex.solution` is written `by exact @_root_.P2MW.S_Module_exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex.solution` applied to the theorem's binders in order (`_` for anonymous instance binders). The statement is unchanged;

## Proof

The proof applies `P2MW.S_Module_exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex.solution` from `Langlands.AnthropicFLT.P2M.Sol.S_Module_exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex`, which has the same statement. The Markdown of that module outlines the argument.
