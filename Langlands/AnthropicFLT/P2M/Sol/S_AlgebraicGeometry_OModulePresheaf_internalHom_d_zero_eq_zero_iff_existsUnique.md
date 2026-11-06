# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Each FLT command `p2m_reactivate "N₁ N₂ …"` (from `P2M.Util`; it re-activates the scoped declarations of the namespaces) is replaced by `open scoped N₁ N₂ …`.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique`.

Proof (namespace `HomGlueAux`): the internal Hom presheaf satisfies the sheaf condition for an ordered affine
cover `K` when `G` is quasi-coherent. Namespace `Idx`: the `0`-simplices `single i` and `1`-simplices `pair a b`
of the cover, with their faces and intersections. `d_zero_apply` unfolds the Čech differential in degree `0`, and
`d_zero_res_eq_zero` shows that restrictions of a global section form a cocycle. Section `InternalHom`: for a
`0`-cochain `c`, `comp K c s D` is the component of `c s` at an affine `D` inside the chart; if `c` is a cocycle,
these components agree on affines contained in two charts (`agree_of_lt`, `agree`).

Gluing (section `Glue`): every affine `W` is covered by finitely many basic opens `D(g j)` of `W`, each inside some
chart (`CoverData`, `nonempty_coverData`). For `x ∈ F(W)`, the local values `loc x j` (the chart components
applied to the restriction of `x`) agree on the overlaps (`loc_compat`) and glue to a unique `glueFun W x ∈ G(W)`
by the ported theorems `exists_forall_res_basicOpen_eq` and `eq_zero_of_forall_res_basicOpen_eq_zero` (for
quasi-coherent `G`). `glueFun` is characterised by its restriction to every affine inside a chart
(`char_of_spec`, `glueFun_char`), hence additive, linear and natural in `W` (`glueFun_add` …
`glueFun_natural`), giving a global section `glued` that restricts to `c s` on every chart (`res_glued`). Two
global sections with equal restrictions to all charts are equal (`res_top_ext`, again by the basic-open
uniqueness). `main` proves the equivalence: a cocycle has the unique preimage `glued`, and conversely
restrictions of a global section form a cocycle. `solution` is `HomGlueAux.main`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.Idx.single`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.Idx.single_val`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.Idx.eq_single`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.Idx.ext0`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.Idx.U_le_inter_single`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.Idx.inter_single_le`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.Idx.inter_le_U0`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.Idx.pair`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.Idx.face_pair_zero`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.Idx.face_pair_one`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.Idx.inter_pair_le_left`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.Idx.inter_pair_le_right`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.Idx.le_inter_pair`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.d_zero_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.d_zero_res_eq_zero`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.res_val`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.comp`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.comp_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.comp_smul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.comp_natural`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.agree_of_lt`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.agree`
- structure `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.CoverData`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.nonempty_coverData`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.coverData`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.CoverData.D`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.CoverData.D_le`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.CoverData.DD`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.CoverData.DD_le_left`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.CoverData.DD_le_right`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.loc`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.loc_compat`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.exists_glue`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.glue_unique`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.glueFun`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.glueFun_spec`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.eq_glueFun`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.glueFun_add`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.glueFun_smul`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.glueFun_smulR`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.glueLin`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.glueLin_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.basicOpen_res_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.char_of_spec`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.glueFun_char`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.glueFun_natural`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.glued`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.glued_val_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.res_glued`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.res_top_ext`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.HomGlueAux.main`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_internalHom_d_zero_eq_zero_iff_existsUnique.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_res_basicOpen_eq` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_eq_zero_of_forall_res_basicOpen_eq_zero` (Library).
Other imports: `Mathlib`.
