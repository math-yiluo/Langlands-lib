# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_iso_glueOfCocycle_app_eq_glueFrame`

## Source

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_iso_glueOfCocycle_app_eq_glueFrame.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem
(commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2"). The text is the FLT text except for the changes listed below.
Licence: Apache License 2.0, Copyright 2026 Anthropic, PBC; unmodified copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice is recorded for it.
The Lean file starts with a notice recording the modification.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`,
  `backward.isDefEq.respectTransparency.types false`.
- `import P2M.Util` (the command library of FLT's build tooling) is dropped, and its commands are replaced by standard Lean commands. Write `N` for this file's namespace `P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_iso_glueOfCocycle_app_eq_glueFrame`. The `_root_.` prefix makes a name refer to the global namespace; inside `N` and its subnamespaces the plain name could resolve to a namespace of this file.
  - FLT line 12: `p2m_open "CategoryTheory Opposite TopologicalSpace CategoryTheory.MonoidalCategory AlgebraicGeometry N.AlgebraicGeometry"` becomes `open CategoryTheory Opposite TopologicalSpace CategoryTheory.MonoidalCategory AlgebraicGeometry`. The namespace `N.AlgebraicGeometry` is omitted: at that point of the file it does not exist yet, and standard `open` rejects an unknown namespace, whereas `p2m_open` records the open declaration without checking. The file compiles without it.
  - FLT line 17: `p2m_export "AlgebraicGeometry" "…"` with 10 names becomes `export _root_.AlgebraicGeometry (…)` with the same names.
  - FLT line 19: `p2m_export "AlgebraicGeometry.Scheme" "…"` with 11 names becomes `export _root_.AlgebraicGeometry.Scheme (…)` with the same names.
  - FLT line 21: `p2m_export "AlgebraicGeometry.Scheme.Modules" "…"` with 9 names becomes `export _root_.AlgebraicGeometry.Scheme.Modules (…)` with the same names.
  - FLT line 23: `p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"` becomes `open _root_.AlgebraicGeometry.Scheme.Modules _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry`.
  - FLT line 25: `p2m_open "AlgebraicGeometry.Scheme.Modules.GlueOfCocycle"` becomes `open AlgebraicGeometry.Scheme.Modules.GlueOfCocycle`.
- No other change: the declarations, statements and proofs are the FLT text.

## Mathematical content

`solution` states: let the opens `U i` cover `X`, let `c` be a unit cocycle on them, and let `M` be a sheaf
of modules with frames `e i` on `U i` (`IsFrameOn (e i) (U i)`) satisfying the transition rule
`e j = c.u i j • e i` on `U i ⊓ U j`. Then there is an isomorphism `φ : M ≅ glueOfCocycle c` with
`φ (e i) = glueFrame c i` for every `i`.

Proof as implemented: the glued module carries the frames `f i = glueFrame c i`, which satisfy the same
transition rule (`isFrameOn_glueFrame`, `map_glueFrame_eq_smul`). For each open `W` let `S W` be the set of
pairs `(u • e i|_W, u • f i|_W)` with `W ⊆ U i` and `u` a unit of `Γ(X, W)`. Every pair in `S W` consists of
two frames on `W` (helper `isFrameOn_unit_smul_map`: a unit multiple of a restricted frame is a frame); the
sets `S W` cover `X`, are stable under restriction, and any two pairs in `S W` differ by one common
coefficient `w` in both components (computed from the transition rule and the inverse of the unit). The LB2
lemma `exists_iso_app_eq_of_isFrameOn_of_eq_smul` turns such a compatible system of pairs of frames into an
isomorphism `φ` mapping the first component of each pair to the second; for the pair `(e i, f i)` on `U i`
this is the asserted identity. The helpers `map_smul'`, `map_map` and `map_refl` are restriction identities
for sections of `M`.

## Contents

Declarations, with their original FLT names and namespaces (no new definitions or statements are introduced):

- theorem `map_smul'`
- theorem `map_map`
- theorem `map_refl`
- theorem `isFrameOn_unit_smul_map`
- theorem `solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor`, `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle`, `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_isFrameOn_of_eq_smul`.
