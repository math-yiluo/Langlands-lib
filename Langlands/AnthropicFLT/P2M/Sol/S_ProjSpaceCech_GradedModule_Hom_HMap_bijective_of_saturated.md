# `Langlands.AnthropicFLT.P2M.Sol.S_ProjSpaceCech_GradedModule_Hom_HMap_bijective_of_saturated`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_ProjSpaceCech_GradedModule_Hom_HMap_bijective_of_saturated.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept.
- 1 `p2m_open_scoped "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that activates the scoped extensions of the named namespaces without opening them) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces; a trailing ` in` is kept.
- 3 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_ProjSpaceCech_GradedModule_Hom_HMap_bijective_of_saturated.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_GradedModule_Hom_HMap_bijective_of_saturated`. Statement. `ProjSpaceCech.GradedModule.Hom.HMap_bijective_of_saturated`: an injective morphism `D₁ → D₂` of graded modules whose
image is saturated (every element of `D₂` becomes, after multiplication by a power of each `x_j`, an image of `D₁`)
induces isomorphisms on Čech cohomology in all degrees.

Proof. By the ported `ProjSpaceCech.GradedModule.Hom.cochainMap_bijective_of_saturated` the map of Čech complexes is
bijective termwise; conclude with the ported `ProjSpaceCech.GradedModule.HMap_bijective_of_cochainMap_bijective`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_ProjSpaceCech_GradedModule_Hom_HMap_bijective_of_saturated.ProjSpaceCech.GradedModule.GradedModule.Hom.HMap_bijective_of_saturated'`
- theorem `P2MW.S_ProjSpaceCech_GradedModule_Hom_HMap_bijective_of_saturated.ProjSpaceCech.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule` (Library), `Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_GradedModule_Hom_cochainMap_bijective_of_saturated` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_ProjSpaceCech_GradedModule_HMap_bijective_of_cochainMap_bijective` (same contribution).
Other imports: `Mathlib`.
