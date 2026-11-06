# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_pow`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_pow.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Each FLT command `p2m_export "N" "a b …"` (from `P2M.Util`; it adds the aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) is replaced by the Lean command `export _root_.N (a b …)`, which adds the same aliases.
- Each FLT command `p2m_open "N₁ N₂ …"` (from `P2M.Util`; it opens the namespaces with their exact names, `N~x~y` hiding `x` and `y`) is replaced by `open _root_.N₁ _root_.N₂ …`, and `N~x~y` by `open _root_.N hiding x y`.
- `p2m_open` also opens namespaces of this module before they exist (later commands create them): `P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_pow.AlgebraicGeometry`. Lean's `open` rejects a namespace that does not exist yet, so each of them is registered by an empty block `namespace N end N` right after the options; the `open` then has the FLT effect.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_pow.solution` proves the statement of the
companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_pow`.

Proof. `G4T.isQuasicoherent_pow` (namespace `AlgebraicGeometry.OModulePresheaf.G4T` inside the solution
namespace) checks the two localisation conditions componentwise for the finite power `F.pow n` (sections
`Fin n → F(U)`): for extension, choose exponents `m i` for the components and multiply the `i`-th lift by
`f^(∑ m - m i)`, so that the common exponent `∑ m` works; for injectivity, the common exponent `∑ m` kills every
component. `solution` is this lemma.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_pow.AlgebraicGeometry.P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_pow.AlgebraicGeometry.OModulePresheaf.G4T.isQuasicoherent_pow`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_pow.AlgebraicGeometry.P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_pow.AlgebraicGeometry.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions` (Library).
Other imports: `Mathlib.AlgebraicGeometry.Morphisms.Separated`, `Mathlib.AlgebraicGeometry.Noetherian`, `Mathlib.RingTheory.Localization.Away.Basic`.
