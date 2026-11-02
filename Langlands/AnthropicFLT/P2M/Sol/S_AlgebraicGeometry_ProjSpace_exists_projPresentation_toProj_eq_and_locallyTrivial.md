# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 3 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept. Namespaces that do not exist at that point of the file are dropped, since standard `open` rejects them (`unknown namespace`); the file compiles without them:
  - `open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.TopologicalSpace _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial.AlgebraicGeometry _root_.MvPolynomial _root_.HomogeneousLocalization`: namespace `P2MW.S_AlgebraicGeometry_ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial.AlgebraicGeometry` dropped.
- 2 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial`. Statement. `AlgebraicGeometry.ProjSpace.exists_projPresentation_toProj_eq_and_locallyTrivial`: for every morphism
`φ : X ⟶ ℙⁿ_A`, there are a module `L` on `X` (the pullback `φ^* 𝒪(1)`) and a `ProjPresentation` of `L`
over `φ ≫ ProjSpace.π A n` with `n + 1` sections whose morphism to projective space is `φ`, such that `L`
is locally trivial (every point has an open neighbourhood on which `L` is isomorphic to the structure
sheaf).

Proof (namespace `AlgebraicGeometry.ProjSpace.PRES`). The charts `U i = φ⁻¹ D₊(Xᵢ)` cover `X`
(`exists_mem_U`), and the frame units `fu i j` (pullbacks of `Xⱼ/Xᵢ`) form a unit cocycle (`fu_self`,
`fu_cocycle`, `cocycle`). Glue the module `L = glueOfCocycle (cocycle φ)` (FLT gluing of modules from a
unit cocycle). The sections `σᵢ` glued from the local functions `fu k i` (`σ`, `map_σ`, `map_σ_of_le`)
form a frame of `L` on `U i` (`isFrameOn_glueFrame`) and satisfy `fu i j · σᵢ = σⱼ`
(`fu_smul_map_σ`), giving the presentation `pres` with `toProj = φ`. Local triviality on `U i` is the
ported `Scheme.Modules.IsFrameOn.nonempty_pullback_iso_unit`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial.AlgebraicGeometry.ProjSpace.PRES.U`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial.AlgebraicGeometry.ProjSpace.PRES.fu`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial.AlgebraicGeometry.ProjSpace.PRES.fu_self`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial.AlgebraicGeometry.ProjSpace.PRES.fu_cocycle`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial.AlgebraicGeometry.ProjSpace.PRES.cocycle`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial.AlgebraicGeometry.ProjSpace.PRES.σ`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial.AlgebraicGeometry.ProjSpace.PRES.map_σ`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial.AlgebraicGeometry.ProjSpace.PRES.map_σ_of_le`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial.AlgebraicGeometry.ProjSpace.PRES.fu_smul_map_σ`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial.AlgebraicGeometry.ProjSpace.PRES.exists_mem_U`
- def `P2MW.S_AlgebraicGeometry_ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial.AlgebraicGeometry.ProjSpace.PRES.pres`
- theorem `P2MW.S_AlgebraicGeometry_ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit` (Library).
Other imports: `Mathlib`.
