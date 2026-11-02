# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point`. Statement. `AlgebraicGeometry.exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point`: in the setting of
a scheme `H ⟶ Spec S` representing flat, finitely presented closed subschemes of `X ⟶ Spec S` on affine tests,
for each affine open `V` of `H` there is a closed subscheme `ZV V ⊆ X ×_S Spec Γ(H, V)` whose point is the
inclusion of `V` (the tautological family), transported to a closed subscheme `jV V` of `X ×_S V` that is flat
and finitely presented over `V`, with ideals agreeing on the overlaps of the `X ×_S V`.

Proof. Section `bc`: base-change maps of `X ×_S -`. Section `chart`: `X ×_S Spec Γ(H, V)` is identified with the open
`pr₂⁻¹ V` (`mV`, `eV`). Surjectivity of `pt` applied to `V.fromSpec` gives `ZV V` (section `models`, with
`restrict_model`), transported along `eV` to `jV V`. Section `compat`: on the overlap of `V` and `V'`, both
families restrict to families over affine opens inside `V ∩ V'` with the same point (naturality of `pt`), hence
are isomorphic (injectivity up to isomorphism), so their ideals agree (`ker_comap_eq_of_le`, `ker_comap_inf_eq`,
`idealSheafData_ext_of_opens`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point.USbSol.bcMap_fst`
- theorem `P2MW.S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point.USbSol.bcMap_snd`
- theorem `P2MW.S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point.USbSol.isPullback_bcMap`
- theorem `P2MW.S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point.USbSol.isOpenImmersion_bcMap`
- theorem `P2MW.S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point.USbSol.range_bcMap`
- theorem `P2MW.S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point.USbSol.bcMap_comp`
- abbrev `P2MW.S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point.USbSol.mV`
- scoped instance `P2MW.S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point.USbSol.isOpenImmersion_mV`
- theorem `P2MW.S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point.USbSol.range_mV`
- def `P2MW.S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point.USbSol.eV`
- theorem `P2MW.S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point.USbSol.eV_hom_ι`
- theorem `P2MW.S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point.USbSol.mV_snd`
- abbrev `P2MW.S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point.USbSol.resH`
- theorem `P2MW.S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point.USbSol.spec_resH_fromSpec`
- abbrev `P2MW.S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point.USbSol.nVW`
- theorem `P2MW.S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point.USbSol.nVW_mV`
- theorem `P2MW.S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point.USbSol.isPullback_nVW`
- theorem `P2MW.S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point.USbSol.preimage_mono`
- theorem `P2MW.S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point.USbSol.eV_homOfLE`
- theorem `P2MW.S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point.USbSol.eV_hom_morphismRestrict`
- theorem `P2MW.S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point.USbSol.restrict_model`
- theorem `P2MW.S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point.USbSol.idealSheafData_ext_of_opens`
- theorem `P2MW.S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point.USbSol.ker_comap_eq_of_le`
- theorem `P2MW.S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point.USbSol.ker_comap_inf_eq`
- theorem `P2MW.S_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_JacJ1Iface` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw` (Library).
Other imports: none.
