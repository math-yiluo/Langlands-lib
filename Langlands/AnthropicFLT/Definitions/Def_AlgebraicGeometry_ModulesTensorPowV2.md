# Tensor powers of a sheaf of modules on a scheme

Module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2`, in namespace
`AlgebraicGeometry.Scheme.Modules`. Schemes live in a fixed universe `u`.

## Definitions

For a sheaf of modules `L` on a scheme `X` (with the monoidal structure on `X.Modules` from
`Def_SheafOfModules_Monoidal`):

- `L.tensorPow n` is the `n`-th tensor power, defined by `L.tensorPow 0 = 𝟙` (the structure sheaf) and
  `L.tensorPow (n + 1) = L.tensorPow n ⊗ L`. The lemmas `tensorPow_zero` and `tensorPow_succ` record
  these equations (by `rfl`).
- `tensorPowOneIso L : L.tensorPow 1 ≅ L` is the left unitor `𝟙 ⊗ L ≅ L`.

## Provenance and licence

This file is a port of `Definitions/Def_AlgebraicGeometry_ModulesTensorPowV2.lean` from the Anthropic
Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026
Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE`
and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's. The port makes only these
changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_SheafOfModules_MonoidalV2` is renamed to
  `Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_MonoidalV2`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`.
