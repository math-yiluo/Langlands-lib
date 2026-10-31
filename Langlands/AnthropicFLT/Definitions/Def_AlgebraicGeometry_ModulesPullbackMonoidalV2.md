# Import hub for the monoidal pullback of sheaves of modules (variant 2)

Module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2`, in namespace
`AlgebraicGeometry.Scheme.Modules`.

## Contents

The file declares nothing. It imports `Def_PresheafOfModules_InternalHom`, `Def_SheafOfModules_MonoidalV2`,
`Def_PresheafOfModules_PullbackMonoidal` and `Def_AlgebraicGeometry_ModulesPullbackMonoidal`, so modules
importing it receive the monoidal structure on sheaves of modules and the monoidal pullback functor of
`Def_AlgebraicGeometry_ModulesPullbackMonoidal`. Its only command is an `example` checking that
`pullback₀ f` is Mathlib's `PresheafOfModules.pullback` for a morphism of schemes `f`, which adds no
declaration.

## Provenance and licence

This file is a port of `Definitions/Def_AlgebraicGeometry_ModulesPullbackMonoidalV2.lean` from the
Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_PresheafOfModules_InternalHom`,
  `Definitions.Def_SheafOfModules_MonoidalV2`, `Definitions.Def_PresheafOfModules_PullbackMonoidal` and
  `Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal` are renamed to the corresponding
  `Langlands.AnthropicFLT.Definitions.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`.
