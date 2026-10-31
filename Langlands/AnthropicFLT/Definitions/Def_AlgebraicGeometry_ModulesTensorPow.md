# Import hub for tensor powers of sheaves of modules

Module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPow`, in namespace
`AlgebraicGeometry.Scheme.Modules`.

## Contents

The file declares nothing. It imports `Def_SheafOfModules_Monoidal` and
`Def_AlgebraicGeometry_ModulesTensorPowV2`, so modules importing it receive the monoidal structure on
sheaves of modules and the tensor powers `L.tensorPow n` defined in
`Def_AlgebraicGeometry_ModulesTensorPowV2`.

## Provenance and licence

This file is a port of `Definitions/Def_AlgebraicGeometry_ModulesTensorPow.lean` from the Anthropic Lean
formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026
Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE`
and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's. The port makes only these
changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_SheafOfModules_Monoidal` and
  `Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2` are renamed to
  `Langlands.AnthropicFLT.Definitions.*`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`.
