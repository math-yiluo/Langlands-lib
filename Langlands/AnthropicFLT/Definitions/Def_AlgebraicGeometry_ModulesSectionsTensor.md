# Tensor products of sections of sheaves of modules, and frames

Module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor`, in namespace
`AlgebraicGeometry.Scheme.Modules`. Schemes live in a fixed universe `u`; `L`, `M` are sheaves of
modules on a scheme `X` and `U` is an open of `X`.

## Definitions and results

**Tensor products of sections.**

- `tensorSectionsHom L M` is the morphism of presheaves of modules from the presheaf tensor product
  `L ⊗ M` (of the underlying presheaves) to the sheaf tensor product `L ⊗ M`: the sheafification unit
  followed by `tensorIsoSheafify`.
- `tensorSections s t ∈ Γ(L ⊗ M, U)`, for `s ∈ Γ(L, U)` and `t ∈ Γ(M, U)`, is the image of `s ⊗ t`
  under it (`tensorSections_def`). It is biadditive and `Γ(X, U)`-bilinear (`tensorSections_add_left`,
  `tensorSections_add_right`, `tensorSections_smul_left`, `tensorSections_smul_right`,
  `tensorSections_zero_left`, `tensorSections_zero_right`, `tensorSections_neg_left`,
  `tensorSections_neg_right`, `tensorSections_sum_left`, `tensorSections_sum_right`).
  `tensorSectionsBilin L M U` packages it as a bilinear map (`tensorSectionsBilin_apply`).
- `map_tensorSections` and `map_homOfLE_tensorSections`: restricting `s ⊗ t` to a smaller open gives the
  tensor product of the restrictions.

**Unit section and tensor powers of a section.**

- `unitSection U ∈ Γ(𝟙, U)` is the section `1` of the structure sheaf (`unitSection_def`). It is
  compatible with restriction (`map_unitSection`), `g • unitSection U = g` (`smul_unitSection`), and
  `g ↦ g • unitSection U` is bijective (`smul_unitSection_bijective`).
- `tensorPowSection s n ∈ Γ(L^{⊗n}, U)`, for `s ∈ Γ(L, U)`, is `s^{⊗n}`: the unit section for `n = 0`
  and `s^{⊗n} ⊗ s` for `n + 1` (`tensorPowSection_zero`, `tensorPowSection_succ`,
  `tensorPowSection_one`). It commutes with restriction (`map_tensorPowSection`).

**Frames.** For `s ∈ Γ(M, U)` and an open `V`:

- `IsFrameOn s V` means that for every open `W ⊆ U ∩ V` the map `Γ(X, W) → Γ(M, W)`, `g ↦ g • s|_W`,
  is bijective: `s` trivializes `M` on `U ∩ V`, so `M|_{U∩V} ≅ 𝒪` with `s` corresponding to `1`.
- `IsFrameOn.bijective` unfolds the definition. `IsFrameOn.mono` and `IsFrameOn.of_inf` /
  `IsFrameOn.inf_iff` change `V` (only `U ∩ V` matters), and `IsFrameOn.map` passes to restrictions of
  `s`. `IsFrameOn.existsUnique` and `IsFrameOn.smul_eq_zero_iff` are consequences of bijectivity.
- `isFrameOn_unitSection`: the unit section is a frame of the structure sheaf everywhere.
  `IsFrameOn.map_iso`: frames are carried to frames by isomorphisms of sheaves of modules.

## Provenance and licence

This file is a port of `Definitions/Def_AlgebraicGeometry_ModulesSectionsTensor.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_PresheafOfModules_InternalHom`,
  `Definitions.Def_SheafOfModules_Monoidal` and `Definitions.Def_AlgebraicGeometry_ModulesTensorPow` are
  renamed to `Langlands.AnthropicFLT.Definitions.*`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- one proof step is adapted to the pinned Mathlib (FLT pins Lean 4.33.1 and Mathlib `db584cd6`; this
  project pins Lean 4.34.0 and Mathlib `5ed29652`, where the presheaf monoidal lemma
  `Monoidal.tensorObj_map_tmul` lives in the namespace `PresheafOfModulesOfCommRing`). The diff against
  the FLT file (after the import rename and option insertion) is:

```diff
--- FLT/Definitions/Def_AlgebraicGeometry_ModulesSectionsTensor.lean (imports rewritten, options inserted)
+++ port
@@ -118,3 +118,3 @@
     ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U)))
-  erw [PresheafOfModules.Monoidal.tensorObj_map_tmul] at h
+  erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul] at h
   exact h.symm
```

The line numbers refer to the file without the attribution header.
