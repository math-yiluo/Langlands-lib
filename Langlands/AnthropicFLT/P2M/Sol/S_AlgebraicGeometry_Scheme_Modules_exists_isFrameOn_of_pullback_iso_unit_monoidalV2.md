# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit_monoidalV2`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit_monoidalV2.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 4 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept. Namespaces that do not exist at that point of the file are dropped, since standard `open` rejects them (`unknown namespace`); the file compiles without them:
  - `open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit_monoidalV2.AlgebraicGeometry`: namespace `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit_monoidalV2.AlgebraicGeometry` dropped.
- 4 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit_monoidalV2.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit_monoidalV2`. Statement. `AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit_monoidalV2`: if the restriction of `M`
to an open `U` is isomorphic to the structure sheaf of `U`, then `M` has a frame on `U` (a section `s` over
`U` with `g ↦ g · s|_V` bijective for all `V ⊆ U`).

Proof. Restriction to the open subscheme `U` is identified with pullback along `U.ι`
(`restrictFunctor'IsoPullback`); the image `gen₀` of `1` under the inverse of the trivialization is a
section over `U` (`TrivializationBelow`, `trivializationBelow`), and multiplication by it on every `V ⊆ U` is
the trivialization, hence bijective.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- structure `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit_monoidalV2.PresheafOfModules.FrameBridge.TrivializationBelow`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameBridge.restrictRingCatSheafHom`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameBridge.restrictFunctor'`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameBridge.restrictFunctor'_eq`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameBridge.restrictFunctor'IsoPullback`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameBridge.image_preimage_of_le`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameBridge.gen₀`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameBridge.gen₀_spec`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameBridge.gen₀_bijective`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameBridge.gen₀_map`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameBridge.bijective_smul_map_eqToHom`
- def `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit_monoidalV2.AlgebraicGeometry.Scheme.Modules.FrameBridge.trivializationBelow`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit_monoidalV2.AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit_monoidalV2.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2` (Library).
Other imports: `Mathlib`.
