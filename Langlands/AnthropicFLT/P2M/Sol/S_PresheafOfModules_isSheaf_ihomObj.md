# The internal hom of presheaves of modules into a sheaf is a sheaf

`Langlands.AnthropicFLT.P2M.Sol.S_PresheafOfModules_isSheaf_ihomObj` proves the theorem `P2MW.S_PresheafOfModules_isSheaf_ihomObj.solution`. Its statement is that of `PresheafOfModules.isSheaf_ihomObj`, which `Langlands.AnthropicFLT.Theorems.Thm_PresheafOfModules_isSheaf_ihomObj` states under its FLT name.

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

The Lean file is ported from `P2M/Sol/S_PresheafOfModules_isSheaf_ihomObj.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed, and its commands are replaced by the equivalent standard Lean commands: `p2m_export` by `export`, `p2m_open` by `open` (with `hiding` where it hid names), `p2m_reactivate` by `open scoped`; a command left with nothing to open or export is dropped. No declaration, statement or proof step changed;

## Proof outline

The sheaf condition for a presheaf of abelian groups is that of its
underlying presheaf of types (`Presheaf.isSheaf_iff_isSheaf_comp`,
`isSheaf_iff_isSheaf_of_type`).

1. Mathlib's presheaf `presheafHom F N` of morphisms between the restricted
   presheaves of abelian groups (over the slice categories `Over X`) is a sheaf
   because `N` is (`Presheaf.IsSheaf.hom`).
2. Let `linearSub F N` be the subpresheaf of `presheafHom F N` of those
   morphisms that are linear over `R` at every object over `X`. The maps
   `toPresheafHom` and `ofPresheafHom` are mutually inverse, so the internal
   hom presheaf, as a presheaf of types, is isomorphic to `linearSub F N`
   (`equivLinearSub`, `isoLinearSub`).
3. A subpresheaf of a sheaf is a sheaf if membership is local
   (`Subfunctor.isSheaf_iff`). Suppose `s` lies in `linearSub` after
   restriction along every arrow of a covering sieve. For `r` and `x` over an
   object `Y` above `X`, the elements `s(r • x)` and `r • s(x)` have equal
   restrictions along every arrow of the pulled-back covering sieve: this uses
   the naturality of `s`, the compatibility of the restriction maps of `F` and
   `N` with scalars (`map_smul`), and the hypothesis. Since `N` is separated,
   `s(r • x) = r • s(x)`.

So `linearSub F N` is a sheaf, and hence so is the internal hom presheaf.
