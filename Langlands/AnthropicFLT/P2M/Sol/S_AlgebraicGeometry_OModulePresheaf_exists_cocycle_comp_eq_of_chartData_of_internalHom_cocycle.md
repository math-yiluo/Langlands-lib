# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle`.

Proof (namespace `Y2dAux` for helpers). Simplices of an ordered cover given by vertices, increasing pairs and
triples, with their faces and intersections (`Idx.single`, `le_inter_single`, `Idx.pair`, `face_pair_zero`,
`face_pair_one`, `le_inter_pair`, `Idx.triple`, `face_triple_zero`, `face_triple_one`, `face_triple_two`,
`le_inter_triple`); the Čech differentials in degrees `0` and `1` (`d_zero_apply`, `d_one_apply`); for the internal
Hom, pointwise subtraction (`sub_val_apply`), the value of `d c` on a pair (`d_zero_pair_apply`) and additivity of a
`1`-cocycle on increasing triples (`z_add_of_lt`); `J • ⊤` is preserved by linear maps (`apply_mem_smul_top`),
vanishes in a quotient by `J • ⊤` (`eq_zero_of_mem_smul_top`), and is detected on the components of internal-Hom
cochains (`cochain_val_mem`).

`solution`: `lam k` kills `I^(k+1) GK` (as `I^(k+1)` kills `F k`; `hkill`). Apply the ported theorem
`exists_cocycle_comp_eq_of_chartData_of_components` with `zC i j` the components of the cocycle `z` on the pair
`(i, j)` (additive on triples by `z_add_of_lt`), `YC k i` the components of `Y k` on vertex `i`, and `tC k i j` the
components of `t k`: the identity `ht` gives the first hypothesis, and `z − t k − d (Y k) ∈ I^(k+1)` together with
`hkill` gives `lam k ∘ zC = lam k ∘ (tC + YC_j − YC_i)`; `hY` and `hkill` give `lam k ∘ YC (k+1) = lam k ∘ YC k`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle.Y2dAux.Idx.single`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle.Y2dAux.Idx.le_inter_single`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle.Y2dAux.Idx.pair`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle.Y2dAux.Idx.face_pair_zero`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle.Y2dAux.Idx.face_pair_one`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle.Y2dAux.Idx.le_inter_pair`
- def `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle.Y2dAux.Idx.triple`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle.Y2dAux.Idx.face_triple_zero`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle.Y2dAux.Idx.face_triple_one`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle.Y2dAux.Idx.face_triple_two`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle.Y2dAux.Idx.le_inter_triple`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle.Y2dAux.d_zero_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle.Y2dAux.d_one_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle.Y2dAux.sub_val_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle.Y2dAux.d_zero_pair_apply`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle.Y2dAux.z_add_of_lt`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle.Y2dAux.apply_mem_smul_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle.Y2dAux.eq_zero_of_mem_smul_top`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle.Y2dAux.cochain_val_mem`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_components` (same contribution).
Other imports: `Mathlib`.
