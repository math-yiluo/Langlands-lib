# The internal hom of presheaves of modules into a sheaf is a sheaf

`Langlands.AnthropicFLT.Theorems.Thm_PresheafOfModules_isSheaf_ihomObj` proves the theorem `PresheafOfModules.isSheaf_ihomObj`.

## Statement

Let `C` be a category (objects and morphisms in universe `u`) with a
Grothendieck topology `J`, `R` a presheaf of commutative rings on `C`, and
`F`, `N` presheaves of modules over `R`. Let `PresheafOfModules.ihomObj F N`
be the internal hom of the FLT module `Definitions.Def_PresheafOfModules_InternalHom`:
its sections over `X` are the natural families, which assign to every arrow
`X ⟶ Y` of `Cᵒᵖ` an `R(Y)`-linear map `F(Y) → N(Y)` compatibly with the
restriction maps of `F` and `N`. If the underlying presheaf of abelian groups
of `N` is a sheaf for `J`, then so is that of `ihomObj F N`.

## Provenance and licence

The Lean file is ported from `Theorems/Thm_PresheafOfModules_isSheaf_ihomObj.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util` is removed, and the proof `by p2m_exact_reverting @_root_.P2MW.S_PresheafOfModules_isSheaf_ihomObj.solution` is written `by exact @_root_.P2MW.S_PresheafOfModules_isSheaf_ihomObj.solution` applied to the theorem's binders in order (`_` for anonymous instance binders). The statement is unchanged;

## Proof

The proof applies `P2MW.S_PresheafOfModules_isSheaf_ihomObj.solution` from `Langlands.AnthropicFLT.P2M.Sol.S_PresheafOfModules_isSheaf_ihomObj`, which has the same statement. The Markdown of that module outlines the argument.
