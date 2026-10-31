# A morphism of sheaves that is an isomorphism on a basis is an isomorphism

`Langlands.AnthropicFLT.Theorems.Thm_TopCat_Sheaf_isIso_of_isIso_app_of_isBasis` proves the theorem `TopCat.Sheaf.isIso_of_isIso_app_of_isBasis`.

## Statement

Let `C` be a category, `X` a topological space and `B : ι → Opens X` a family of
open sets whose range is a basis of the topology (`Opens.IsBasis (Set.range B)`).
Let `φ : F ⟶ G` be a morphism of `C`-valued sheaves on `X`. If the component
`φ.1.app (op (B i))` is an isomorphism for every index `i`, then `φ` is an
isomorphism. The universes of `C`, of its morphisms, of `X` and of `ι` are
arbitrary.

## Provenance and licence

The Lean file is ported from `Theorems/Thm_TopCat_Sheaf_isIso_of_isIso_app_of_isBasis.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_TopCat_Sheaf_isIso_of_isIso_app_of_isBasis.solution` is written `by exact @_root_.P2MW.S_TopCat_Sheaf_isIso_of_isIso_app_of_isBasis.solution` applied to the theorem's binders in order (`_` for anonymous instance binders). The statement is unchanged;

## Proof

The proof applies `P2MW.S_TopCat_Sheaf_isIso_of_isIso_app_of_isBasis.solution` from `Langlands.AnthropicFLT.P2M.Sol.S_TopCat_Sheaf_isIso_of_isIso_app_of_isBasis`, which has the same statement. The Markdown of that module outlines the argument.
