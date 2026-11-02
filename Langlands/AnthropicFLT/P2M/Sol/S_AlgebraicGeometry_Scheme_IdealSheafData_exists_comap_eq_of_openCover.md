# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 4 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- 2 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept. Namespaces that do not exist at that point of the file are dropped, since standard `open` rejects them (`unknown namespace`); the file compiles without them:
  - `open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.AlgebraicGeometry _root_.TopologicalSpace`: namespace `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.AlgebraicGeometry` dropped.
- 3 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover`. Statement. `AlgebraicGeometry.Scheme.IdealSheafData.exists_comap_eq_of_openCover` (gluing ideal sheaves): for an open
cover `𝒰` of `X` and ideal sheaves `Iᵢ` on the members whose pullbacks agree on all overlaps (for every
pair of maps `a, b` from a scheme with `a ≫ 𝒰.f i = b ≫ 𝒰.f j`), there is an ideal sheaf `I₀` on `X`
restricting to `Iᵢ` on each member.

Proof. For an affine open `U` of `X`, define the ideal `J U` as the set of sections whose restrictions to
the affine opens `imA` of the members (images of affine opens of `𝒰.X i` contained in `U`) lie in the
corresponding ideals of `Iᵢ` (`T`, `J`); the compatibility on overlaps makes this independent of the
member. Section `L3`: `J` satisfies the conditions of `IdealSheafData` (compatibility with restriction
to basic opens), giving `glued`, and `comap_glued` checks that its pullback to each member is `Iᵢ`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- lemma `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.AlgebraicGeometry.Scheme.IdealSheafData.Glue.appIso_of_comp_eq`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.AlgebraicGeometry.Scheme.IdealSheafData.Glue.image_eq_of_comp_eq`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.AlgebraicGeometry.Scheme.IdealSheafData.Glue.mem_map_iff_of_bijective`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.AlgebraicGeometry.Scheme.IdealSheafData.Glue.appIso_hom_naturality_apply`
- def `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.AlgebraicGeometry.Scheme.IdealSheafData.Glue.imA`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.AlgebraicGeometry.Scheme.IdealSheafData.Glue.coe_imA`
- def `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.AlgebraicGeometry.Scheme.IdealSheafData.Glue.T`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.AlgebraicGeometry.Scheme.IdealSheafData.Glue.T_eq_comap`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.AlgebraicGeometry.Scheme.IdealSheafData.Glue.T_map_of_le`
- def `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.AlgebraicGeometry.Scheme.IdealSheafData.Glue.J`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.AlgebraicGeometry.Scheme.IdealSheafData.Glue.mem_J_iff`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.AlgebraicGeometry.Scheme.IdealSheafData.Glue.J_map_le`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.AlgebraicGeometry.Scheme.IdealSheafData.Glue.T_eq_of_image_eq`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.AlgebraicGeometry.Scheme.IdealSheafData.Glue.J_imA`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.AlgebraicGeometry.Scheme.IdealSheafData.Glue.presheaf_map_eq`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.AlgebraicGeometry.Scheme.IdealSheafData.Glue.presheaf_map_map_apply`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.AlgebraicGeometry.Scheme.IdealSheafData.Glue.mem_ideal_of_forall_basicOpen`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.AlgebraicGeometry.Scheme.IdealSheafData.Glue.algebraMap_basicOpen_apply`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.AlgebraicGeometry.Scheme.IdealSheafData.Glue.J_map_congr`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.AlgebraicGeometry.Scheme.IdealSheafData.Glue.J_basicOpen_basicOpen`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.AlgebraicGeometry.Scheme.IdealSheafData.Glue.mem_J_of_forall_basicOpen`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.AlgebraicGeometry.Scheme.IdealSheafData.Glue.exists_good_cover`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.AlgebraicGeometry.Scheme.IdealSheafData.Glue.J_basicOpen_le'`
- lemma `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.AlgebraicGeometry.Scheme.IdealSheafData.Glue.J_basicOpen_le`
- def `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.AlgebraicGeometry.Scheme.IdealSheafData.Glue.glued`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.AlgebraicGeometry.Scheme.IdealSheafData.Glue.comap_glued`
- theorem `P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_comap_eq_of_openCover.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`, `Mathlib.AlgebraicGeometry.Cover.Open`.
