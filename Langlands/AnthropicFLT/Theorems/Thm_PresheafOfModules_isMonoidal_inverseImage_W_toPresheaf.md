# Local isomorphisms of presheaves of modules are stable under tensor products

`Langlands.AnthropicFLT.Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf` proves the theorem `PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf`.

## Statement

Let `C` be a category (objects and morphisms in universe `u`) with a
Grothendieck topology `J`, `𝒪` a presheaf of commutative rings on `C`, `R` a
sheaf of rings and `α : 𝒪 ⟶ R` a morphism of presheaves of rings that is
locally injective and locally surjective. Assume that `J.W` for abelian groups
coincides with the locally bijective morphisms and that weak sheafification
of presheaves of abelian groups exists. Let `W` be the class of morphisms of
presheaves of `𝒪`-modules whose underlying morphism of presheaves of abelian
groups lies in `J.W`, that is, becomes an isomorphism after sheafification.
Then `W` is monoidal (`MorphismProperty.IsMonoidal`) for the tensor product of
presheaves of modules: it is stable under whiskering on both sides.

## Provenance and licence

The Lean file is ported from `Theorems/Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf.solution` is written `by exact @_root_.P2MW.S_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf.solution` applied to the theorem's binders in order (`_` for anonymous instance binders). The statement is unchanged;

## Proof

The proof applies `P2MW.S_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf.solution` from `Langlands.AnthropicFLT.P2M.Sol.S_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf`, which has the same statement. The Markdown of that module outlines the argument.
