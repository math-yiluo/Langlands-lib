# A finite flat module of constant rank is finitely presented

`Langlands.AnthropicFLT.Theorems.Thm_Module_finitePresentation_of_rankAtStalk_eq` proves the theorem `Module.finitePresentation_of_rankAtStalk_eq`.

## Statement

Let `R` be a commutative ring and `M` a finite flat `R`-module whose rank at
every prime is the same number `n`: for every prime `p`, the free module
`M_p` over the local ring `R_p` has rank `n` (`Module.rankAtStalk M p = n`).
Then `M` is a finitely presented `R`-module.

## Provenance and licence

The Lean file is ported from `Theorems/Thm_Module_finitePresentation_of_rankAtStalk_eq.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_Module_finitePresentation_of_rankAtStalk_eq.solution` is written `by exact @_root_.P2MW.S_Module_finitePresentation_of_rankAtStalk_eq.solution` applied to the theorem's binders in order (`_` for anonymous instance binders). The statement is unchanged;

## Proof

The proof applies `P2MW.S_Module_finitePresentation_of_rankAtStalk_eq.solution` from `Langlands.AnthropicFLT.P2M.Sol.S_Module_finitePresentation_of_rankAtStalk_eq`, which has the same statement. The Markdown of that module outlines the argument.
