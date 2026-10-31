# Čech 0-cocycles of a sheaf of modules are its global sections (proof)

Module
`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_d_zero_ofModules_eq_zero_iff_existsUnique`.
Its declarations live in the namespace
`P2MW.S_AlgebraicGeometry_OModulePresheaf_d_zero_ofModules_eq_zero_iff_existsUnique`.

## Statement

`solution`: for `π : V ⟶ Spec R`, a sheaf of modules `M : V.Modules`, an ordered affine cover `K` of `V` and a
Čech `0`-cochain `c` of `OModulePresheaf.ofModules π M` (`Def_AlgebraicGeometry_OModulePresheafOfModules`),
`c` is a cocycle (its Čech differential vanishes) if and only if there is a unique global section
`x : Γ(M, ⊤)` whose restriction to `K.inter s` is `c s` for every `0`-index `s`. The theorem module
`Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_zero_ofModules_eq_zero_iff_existsUnique` states this as
`AlgebraicGeometry.OModulePresheaf.d_zero_ofModules_eq_zero_iff_existsUnique` and proves it from `solution`.

## Proof outline

The proof is `main` in the namespace `…CechH0Sol` (section `cechH0`).

1. **Indices.** `map_map` and `map_id'` compose and remove restrictions. `idx0 i` is the `0`-index at the open
   `K.U i`, every `0`-index has this form (`exists_eq_idx0`), and `K.inter (idx0 i) = K.U i` (`le_inter_idx0`,
   `inter_idx0_le`). For `i < j`, `idx1 h` is the `1`-index `(i, j)`, with faces `idx0 j` and `idx0 i`
   (`face_idx1_zero`, `face_idx1_one`) and intersection `K.U i ⊓ K.U j` (`inf_le_inter_idx1`). `map_congr_idx`
   transports along equal indices, and `d_zero_apply` writes the degree-`0` differential as the difference of
   the two restrictions.
2. **Gluing.** `sfam c` is the family of sections of `M` on the opens `K.U i` given by `c`. If it is
   compatible on overlaps, the sheaf property of `M` (`TopCat.Sheaf.existsUnique_gluing'`, the opens cover
   `V`) gives a unique global section restricting to it (`glue`).
3. **`main`.** If `d c = 0`, then evaluating at `idx1 h` shows that `sfam c` is compatible (for `i < j`; the
   cases `i = j` and `i > j` follow), so `glue` gives the unique `x`. Conversely, if all `c s` are
   restrictions of one global section `x`, both terms of `d c` at every `1`-index are restrictions of `x`, so
   they cancel.

## Provenance and licence

This file is a port of
`P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_d_zero_ofModules_eq_zero_iff_existsUnique.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic,
PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and
`ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` and
  `Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules` are renamed to the corresponding
  `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed; the file used none of its commands.
