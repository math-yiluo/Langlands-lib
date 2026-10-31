# H⁰ of a two-term complex with fibre dimension at most one is locally an annihilator

`Langlands.AnthropicFLT.Theorems.Thm_CoherentBaseChange_TwoTermComplex_exists_nonempty_H0_linearEquiv_annihilator_of_fibreH0_le_one` proves the theorem `CoherentBaseChange.TwoTermComplex.exists_nonempty_H0_linearEquiv_annihilator_of_fibreH0_le_one`.

## Statement

Let `R` be a commutative ring and `G` a two-term complex over `R` (the FLT
structure `CoherentBaseChange.TwoTermComplex`: a linear map `d : C0 → C1`
between finite free `R`-modules). For an `R`-algebra `B`, `G.H0 B` is the
kernel of `B ⊗ d`. Let `𝔭` be a prime of `R` with residue field `κ` such that
`G.fibreH0 𝔭 = dim_κ ker (κ ⊗ d) ≤ 1`. Then there are `h ∈ R` with `h ∉ 𝔭`
and an ideal `J` of `R` such that for every `R`-algebra `B` in which `h` is a
unit, `G.H0 B` is isomorphic, as a `B`-module, to the annihilator in `B` of
the extended ideal `J B`.

## Provenance and licence

The Lean file is ported from `Theorems/Thm_CoherentBaseChange_TwoTermComplex_exists_nonempty_H0_linearEquiv_annihilator_of_fibreH0_le_one.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_CoherentBaseChange_TwoTermComplex_exists_nonempty_H0_linearEquiv_annihilator_of_fibreH0_le_one.solution` is written `by exact @_root_.P2MW.S_CoherentBaseChange_TwoTermComplex_exists_nonempty_H0_linearEquiv_annihilator_of_fibreH0_le_one.solution` applied to the theorem's binders in order (`_` for anonymous instance binders). The statement is unchanged;

## Proof

The proof applies `P2MW.S_CoherentBaseChange_TwoTermComplex_exists_nonempty_H0_linearEquiv_annihilator_of_fibreH0_le_one.solution` from `Langlands.AnthropicFLT.P2M.Sol.S_CoherentBaseChange_TwoTermComplex_exists_nonempty_H0_linearEquiv_annihilator_of_fibreH0_le_one`, which has the same statement. The Markdown of that module outlines the argument.
