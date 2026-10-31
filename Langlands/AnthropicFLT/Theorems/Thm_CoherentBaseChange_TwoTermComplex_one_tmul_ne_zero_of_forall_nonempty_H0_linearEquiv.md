# A generator of the kernel of a two-term complex with free rank-one H⁰ is unimodular

`Langlands.AnthropicFLT.Theorems.Thm_CoherentBaseChange_TwoTermComplex_one_tmul_ne_zero_of_forall_nonempty_H0_linearEquiv` proves the theorem `CoherentBaseChange.TwoTermComplex.one_tmul_ne_zero_of_forall_nonempty_H0_linearEquiv`.

## Statement

Let `R` be a commutative ring and `G` a two-term complex over `R` (the FLT
structure `CoherentBaseChange.TwoTermComplex`: a linear map `d : C0 → C1`
between finite free `R`-modules). For an `R`-algebra `A`, `G.H0 A` is the
kernel of the base change `A ⊗ d`. Let `g₀ ∈ C0` be such that every element
of `ker d` is an `R`-multiple of `g₀`, and suppose that for every
`R`-algebra `C` (in universe `u`) the `C`-module `G.H0 C` is isomorphic to
`C`. Then for every nontrivial `R`-algebra `C`, the element `1 ⊗ g₀` of
`C ⊗[R] C0` is nonzero.

## Provenance and licence

The Lean file is ported from `Theorems/Thm_CoherentBaseChange_TwoTermComplex_one_tmul_ne_zero_of_forall_nonempty_H0_linearEquiv.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_CoherentBaseChange_TwoTermComplex_one_tmul_ne_zero_of_forall_nonempty_H0_linearEquiv.solution` is written `by exact @_root_.P2MW.S_CoherentBaseChange_TwoTermComplex_one_tmul_ne_zero_of_forall_nonempty_H0_linearEquiv.solution` applied to the theorem's binders in order (`_` for anonymous instance binders). The statement is unchanged;

## Proof

The proof applies `P2MW.S_CoherentBaseChange_TwoTermComplex_one_tmul_ne_zero_of_forall_nonempty_H0_linearEquiv.solution` from `Langlands.AnthropicFLT.P2M.Sol.S_CoherentBaseChange_TwoTermComplex_one_tmul_ne_zero_of_forall_nonempty_H0_linearEquiv`, which has the same statement. The Markdown of that module outlines the argument.
