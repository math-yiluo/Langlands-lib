# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 2 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- 1 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names. The command `export _root_.P2mGlue (isIso_app)` is dropped; see the port edit below.
- Port edit replacing a `P2M.Util` alias (FLT line 121, line 131 here): `haveI : IsIso φ := isIso_app W h` is replaced by `haveI : IsIso φ := _root_.P2mGlue.isIso_app W h`. FLT `p2m_export "P2mGlue" "isIso_app"` aliases the private declaration(s) `_root_.P2mGlue.`, `_root_.isIso_app.` (declared earlier in the file) into the current namespace. Standard `export` cannot do this: `P2mGlue` contains only private declarations and is not a registered namespace (`unknown namespace`). The command is dropped, and the uses of the alias are written with the full name of the private declaration, which denotes the same declaration.
- Port edit replacing a `P2M.Util` alias (FLT line 122, line 132 here): `haveI : IsIso ψ := isIso_app (Y.affineBasicOpen f) ((Y.basicOpen_le f).trans h)` is replaced by `haveI : IsIso ψ := _root_.P2mGlue.isIso_app (Y.affineBasicOpen f) ((Y.basicOpen_le f).trans h)`. FLT `p2m_export "P2mGlue" "isIso_app"` aliases the private declaration(s) `_root_.P2mGlue.`, `_root_.isIso_app.` (declared earlier in the file) into the current namespace. Standard `export` cannot do this: `P2mGlue` contains only private declarations and is not a registered namespace (`unknown namespace`). The command is dropped, and the uses of the alias are written with the full name of the private declaration, which denotes the same declaration.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top`. Statement. `AlgebraicGeometry.Scheme.IdealSheafData.exists_forall_comap_iota_eq_of_iSup_eq_top`: ideal sheaves on the
members of an open cover `(𝒰 j)` of `Y` (indexed by a type in the universe of `Y`) that agree on pairwise
intersections glue to an ideal sheaf `I₀` on `Y` restricting to each of them.

Proof. Section `Maps`: transport of sections along inclusions of opens (`pmap` and its rules).
Section `Locality`: membership in an ideal sheaf on an affine open is checked on a cover by basic opens
(`mem_ideal_of_forall_basicOpen`, `forall_basicOpen_of_mem_ideal`). Sections `T`, `T2`: for an affine open
`U` of `Y`, `T U` is the set of sections whose restriction to every affine open of every member contained in
`U` lies in the corresponding ideal; it is compatible with restriction and basic opens (`T_res`,
`T_basicOpen`, `T_congr`, `mem_T_image`). Section `Glue`: by the compatibility hypothesis (`T_compat`) and
quasi-coherence of ideal sheaves (`exists_pow_mul_mem_T`, `exists_finset_subordinate`,
`exists_pow_mul_res_mem_T`), the ideals `glueIdeal U = T U` form an ideal sheaf (`glue`) whose
restriction to each member is the given one (`comap_glue_ι`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.pmap_congr`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.pmap_pmap`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.pmap_self`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.ideal_cast`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.ideal_res`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.mem_ideal_of_forall_basicOpen`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.forall_basicOpen_of_mem_ideal`
- def `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.pre`
- def `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.T`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.mem_T`
- private theorem `P2mGlue.isIso_app`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.app_pmap`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.mem_T_cast`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.T_res`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.T_basicOpen`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.resV_eq`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.app_eq`
- def `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.toTop`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.isAffineOpen_top'`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.mem_T_iff_comap_homOfLE`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.T_congr`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.mem_T_image`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.basicOpen_pmap_le`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.pmap_pmap_congr`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.T_compat`
- def `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.glueIdeal`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.mem_glueIdeal`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.exists_pow_mul_mem_T`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.exists_finset_subordinate`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.map_glueIdeal_le`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.exists_pow_mul_res_mem_T`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.glueIdeal_basicOpen_le`
- def `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.glue`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.P2mGlue.comap_glue_ι`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_forall_comap_iota_eq_of_iSup_eq_top.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
