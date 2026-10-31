# The presheaf of modules underlying a sheaf of modules on a scheme

Module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules`, in namespace
`AlgebraicGeometry.OModulePresheaf`. All objects live in a fixed universe `u`.

## Definitions

Let `π : V ⟶ Spec R` for a commutative ring `R`, and let `M` be a sheaf of `𝒪_V`-modules
(`V.Modules`).

- `ofModules π M` is the presheaf of modules over `π` (`OModulePresheaf π`) with sections
  `obj U = Γ(M, U)`, the `Γ(V, U)`-module structure of `M`, the `R`-module structure obtained through `π`
  (`moduleSectionsOfHom`), and the restriction maps of `M`.

The lemmas `ofModules_obj`, `ofModules_res_apply`, `ofModules_smul` and `ofModules_algebraMap_smul`
unfold this definition, and `ofModules_twoChartSections` says that its two-chart Čech data for a cover
`𝒱` by two affine opens is `𝒱.sectionsOf π M`. All are proved by `rfl`.

## Provenance and licence

This file is a port of `Definitions/Def_AlgebraicGeometry_OModulePresheafOfModules.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech` and
  `Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf` are renamed to
  `Langlands.AnthropicFLT.Definitions.*`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`.
