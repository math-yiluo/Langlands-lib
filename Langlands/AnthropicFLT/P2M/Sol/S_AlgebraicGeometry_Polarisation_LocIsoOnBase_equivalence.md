# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 2 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept. Namespaces that do not exist at that point of the file are dropped, since standard `open` rejects them (`unknown namespace`); the file compiles without them:
  - `open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence.AlgebraicGeometry _root_.AlgebraicGeometry.Polarisation _root_.P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence.AlgebraicGeometry.Polarisation`: namespace `P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence.AlgebraicGeometry` dropped.
  - `open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Polarisation _root_.P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence.AlgebraicGeometry.Polarisation`: namespace `P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence.AlgebraicGeometry.Polarisation` dropped.
- 4 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names. The command `export _root_.AlgebraicGeometry.Polarisation.LocIsoOnBaseEquivSol (symm)` is dropped; see the port edit below. The command `export _root_.AlgebraicGeometry.Polarisation.LocIsoOnBaseEquivSol (refl)` is dropped; see the port edit below.
- Port edit replacing a `P2M.Util` alias (FLT line 59, line 68 here): `⟨refl g, symm, trans⟩` is replaced by `⟨_root_.AlgebraicGeometry.Polarisation.LocIsoOnBaseEquivSol.refl g, _root_.AlgebraicGeometry.Polarisation.LocIsoOnBaseEquivSol.symm, trans⟩`. FLT `p2m_export "AlgebraicGeometry.Polarisation.LocIsoOnBaseEquivSol" "symm"` aliases the private declaration(s) `_root_.AlgebraicGeometry.Polarisation.LocIsoOnBaseEquivSol.`, `_root_.symm.` (declared earlier in the file) into the current namespace. Standard `export` cannot do this: `AlgebraicGeometry.Polarisation.LocIsoOnBaseEquivSol` contains only private declarations and is not a registered namespace (`unknown namespace`). The command is dropped, and the uses of the alias are written with the full name of the private declaration, which denotes the same declaration. FLT `p2m_export "AlgebraicGeometry.Polarisation.LocIsoOnBaseEquivSol" "refl"` aliases the private declaration(s) `_root_.AlgebraicGeometry.Polarisation.LocIsoOnBaseEquivSol.`, `_root_.refl.` (declared earlier in the file) into the current namespace. Standard `export` cannot do this: `AlgebraicGeometry.Polarisation.LocIsoOnBaseEquivSol` contains only private declarations and is not a registered namespace (`unknown namespace`). The command is dropped, and the uses of the alias are written with the full name of the private declaration, which denotes the same declaration.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence`. Statement. `AlgebraicGeometry.Polarisation.LocIsoOnBase.equivalence`: for `g : X ⟶ Spec S`, the relation
`LocIsoOnBase g` on modules of `X` (local isomorphism over neighbourhoods of the points of the base) is
an equivalence relation.

Proof (namespace `AlgebraicGeometry.Polarisation.LocIsoOnBaseEquivSol`). Reflexivity uses `U = ⊤` and the
identity, symmetry the inverse isomorphism. For transitivity, restrict the two isomorphisms to the
intersection of the two neighbourhoods (`restrictIso`, pulling back along the inclusion
`g⁻¹ V ⊆ g⁻¹ U`) and compose.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- private theorem `AlgebraicGeometry.Polarisation.LocIsoOnBaseEquivSol.refl`
- private theorem `AlgebraicGeometry.Polarisation.LocIsoOnBaseEquivSol.symm`
- def `P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence.AlgebraicGeometry.Polarisation.LocIsoOnBaseEquivSol.restrictIso`
- theorem `P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence.AlgebraicGeometry.Polarisation.LocIsoOnBaseEquivSol.trans`
- theorem `P2MW.S_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_PolarisationRosati` (same contribution).
Other imports: `Mathlib`.
