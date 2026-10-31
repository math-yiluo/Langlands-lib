# Local isomorphisms of presheaves of modules are stable under tensor products

`Langlands.AnthropicFLT.P2M.Sol.S_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf` proves the theorem `P2MW.S_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf.solution`. Its statement is that of `PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf`, which `Langlands.AnthropicFLT.Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf` states under its FLT name.

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

The Lean file is ported from `P2M/Sol/S_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf.lean` of the Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (`anthropic-flt-complete-lean-source-6e837e75`). That source is Copyright 2026 Anthropic, PBC, and licensed under the Apache License, Version 2.0 (see `licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`). The file is not listed in the FLT `ATTRIBUTION.md`, and the Lean file carries an attribution header. The mathematics, the declaration names and the proofs are FLT's. The port makes these changes:

- imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged;
- the options of the FLT lakefile (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`) are set in the file;
- the import of FLT's helper module `P2M.Util`, the command library of FLT's own build tooling, is removed, and its commands are replaced by the equivalent standard Lean commands: `p2m_export` by `export`, `p2m_open` by `open` (with `hiding` where it hid names), `p2m_reactivate` by `open scoped`; a command left with nothing to open or export is dropped. No declaration, statement or proof step changed;
- the FLT proof selects the first and third conditions of
  `Monoidal.Reflective.isIso_tfae` by `.out 0 2`; the pinned Mathlib makes
  `List.TFAE.out` 1-indexed, so the port writes `.out 1 3` for the same two
  conditions.

## Proof outline

Let `shf` be the sheafification functor from presheaves of `𝒪`-modules to
sheaves of `R`-modules, and `inc` its right adjoint, forgetting the sheaf
condition and restricting scalars along `α`. The counit is an isomorphism, so
`inc` is fully faithful.

1. `W` is the class of morphisms inverted by `shf`
   (`PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms`);
   in particular it has the two-out-of-three property.
2. The unit of the adjunction is an isomorphism at every presheaf whose
   underlying presheaf of abelian groups is a sheaf: its underlying morphism
   is `toSheafify`, an isomorphism on sheaves, and the forgetful functor to
   presheaves of abelian groups reflects isomorphisms.
3. Presheaves of modules are monoidal closed, with the internal hom of the FLT
   module `Definitions.Def_PresheafOfModules_InternalHom`. Mathlib's
   `Monoidal.Reflective.isIso_tfae` (Day's reflection theorem) shows that if
   the unit is an isomorphism at every internal hom from a presheaf into a
   sheaf, then `shf` inverts `η_d ▷ d'` for all `d`, `d'`, where `η` is the
   unit. The hypothesis holds by step 2 and
   `PresheafOfModules.isSheaf_ihomObj` (in this port).
4. Let `g : d₁ ⟶ d₂` lie in `W`. Naturality of the unit gives
   `g ≫ η_{d₂} = η_{d₁} ≫ inc (shf g)`; whiskering by `d'`, the morphisms
   `η_{d₁} ▷ d'`, `η_{d₂} ▷ d'` and `inc (shf g) ▷ d'` lie in `W` (the last
   because `inc (shf g)` is an isomorphism), and two-out-of-three gives
   `g ▷ d' ∈ W`.
5. Left whiskering follows from right whiskering through the braiding:
   `d ◁ g` and `g ▷ d` are isomorphic arrows (`MorphismProperty.arrow_mk_iso_iff`).
