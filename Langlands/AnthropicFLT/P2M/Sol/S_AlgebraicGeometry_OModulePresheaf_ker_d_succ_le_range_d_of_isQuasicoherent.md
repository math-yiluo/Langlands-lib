# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 2 `p2m_open "…"` command(s) (an FLT command from `P2M.Util` that opens the named namespaces and activates their scoped extensions, `N~a~b` opening `N` with `a`, `b` hidden; it does not check that a namespace exists) are replaced by standard `open` commands with the same namespaces: `open _root_.N₁ _root_.N₂ …` for the namespaces without hidden names and one `open _root_.N hiding a b` per namespace with hidden names; a trailing ` in` is kept. Namespaces that do not exist at that point of the file are dropped, since standard `open` rejects them (`unknown namespace`); the file compiles without them:
  - `open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Opposite`: namespace `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry` dropped.
- 2 `p2m_export "N" "a b …"` command(s) (an FLT command from `P2M.Util` that adds aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) are replaced by `export _root_.N (a b …)` with the same names.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent`. Statement. `AlgebraicGeometry.OModulePresheaf.ker_d_succ_le_range_d_of_isQuasicoherent` (Čech acyclicity on affine
schemes): for an affine scheme `V`, `π : V ⟶ Spec R` separated, a quasi-coherent FLT presheaf `F` and an
ordered affine cover `K`, every Čech cocycle of degree `i + 1` is a coboundary
(`ker d_{i+1} ≤ range d_i`).

Proof (namespace `AlgebraicGeometry.OModulePresheaf.AffineAcyclicF`), for an ordered affine cover `K` of an
open `W`. Section `AltImg`: combinatorics of strictly increasing index tuples (images, faces, insertion
of an index, positions and signs). Section `FCochain`: Čech cochains `cochainOf` and differentials
`dOf`. Section `WholeSpace`: if one member of the cover is all of `W`, inserting that index defines a
contracting homotopy (`htpy`, `htpy_rel`), so the complex is exact (`wholeSpace_exact`). Section
`AffineAcyclic`: for affine `W`, cochains form `Γ(V, W)`-modules compatible with the differential
(`altd_smulW`); restricting the cover to a basic open `D(f)` inside a member (`restrictBasic`,
`resBasic`) and quasi-coherence (`away_surj`, `away_ker`) show that for a cocycle `z`, some `fᴺ z` is a
coboundary (`smul_pow_mem_range`); since finitely many such `f` (a refinement by basic opens inside the
members, `exists_refinement`) generate the unit ideal, `z` is a coboundary (`affine_acyclic`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.altImg`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.card_altImg`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.altIdx_canonical`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.altIdx_eq_of_altImg`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.altOpen_eq_biInf`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.altImg_altFace`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.altOfFinset`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.altImg_altOfFinset`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.altImg_deg0`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.altPos`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.altIdx_val_altPos`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.altPos_val`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.altInsert`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.altImg_altInsert`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.insPos`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.altInsert_val_insPos`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.altFace_altInsert_insPos`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.altPos_congr`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.altInsert_altFace_altPos`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.insPos_altFace_altPos`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.altFace_altInsert_ne`
- abbrev `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.cochainOf`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.dOf`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.dOf_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.altC_at_eq`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.res_self`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.altOpen_altInsert`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.htpy`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.htpy_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.notMem_altImg_altFace`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.sign_rel`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.htpy_rel`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.wholeSpace_exact`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.isAffineOpen_altOpen`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.moduleW_altC`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.smulW_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.resΓ_resΓ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.resΓ_pow_resΓ`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.altd_smulW`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.rangeW`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.restrictBasic`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.altOpen_restrictBasic`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.altOpen_restrictBasic_le`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.resBasic`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.resBasic_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.altd_resBasic`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.away_surj`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.away_ker`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.exists_refinement`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.smul_pow_mem_range`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.AlgebraicGeometry.OModulePresheaf.AffineAcyclicF.affine_acyclic`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_ker_d_succ_le_range_d_of_isQuasicoherent.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverOf` (Library).
Other imports: `Mathlib.AlgebraicGeometry.Morphisms.Separated`, `Mathlib.RingTheory.LocalProperties.Submodule`, `Mathlib.RingTheory.Localization.Away.Basic`.
