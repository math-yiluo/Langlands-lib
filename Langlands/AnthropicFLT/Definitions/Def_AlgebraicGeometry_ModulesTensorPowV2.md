# Tensor powers of a sheaf of modules on a scheme

Module `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2`, in namespace
`AlgebraicGeometry.Scheme.Modules`. Schemes live in a fixed universe `u`.

## Definitions

For a sheaf of modules `L` on a scheme `X` (with the monoidal structure on `X.Modules` from
`Def_SheafOfModules_Monoidal`):

- `L.tensorPowFLT n` is the `n`-th tensor power, defined by `L.tensorPowFLT 0 = 𝟙` (the structure sheaf) and
  `L.tensorPowFLT (n + 1) = L.tensorPowFLT n ⊗ L`. The lemmas `tensorPowFLT_zero` and `tensorPowFLT_succ` record
  these equations (by `rfl`).
- `tensorPowOneIso L : L.tensorPowFLT 1 ≅ L` is the left unitor `𝟙 ⊗ L ≅ L`.

## Provenance and licence

This file is a port of `Definitions/Def_AlgebraicGeometry_ModulesTensorPowV2.lean` from the Anthropic
Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`
(registered literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026
Anthropic, PBC, and is licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE`
and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no
third-party notice applies. Declaration names and namespaces are FLT's, apart from the renames described under “Names changed by the Library” below. The port makes only these
changes:

- an attribution header is added above the imports;
- the import of the FLT module `Definitions.Def_SheafOfModules_MonoidalV2` is renamed to
  `Langlands.AnthropicFLT.Definitions.Def_SheafOfModules_MonoidalV2`;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`.

## Names changed by the Library (22 November 2026)

weil-conjectures, on which the Library depends, declares 21 of the names of this extract itself, so that no module could import both. The Library renamed these 21 declarations: each keeps its name space and the last component of its name gets the marker `FLT` (`tensorPow` becomes `tensorPowFLT`, `tensorPow_zero` becomes `tensorPowFLT_zero`). In this file:

- it declares `AlgebraicGeometry.Scheme.Modules.tensorPowFLT` (FLT `AlgebraicGeometry.Scheme.Modules.tensorPow`), `AlgebraicGeometry.Scheme.Modules.tensorPowFLT_succ` (FLT `AlgebraicGeometry.Scheme.Modules.tensorPow_succ`), `AlgebraicGeometry.Scheme.Modules.tensorPowFLT_zero` (FLT `AlgebraicGeometry.Scheme.Modules.tensorPow_zero`).

Statements and proofs are otherwise unchanged. Elsewhere on this page the names are given as they now are. The Lean file also imports `Langlands.MathlibBase` where FLT imports `Mathlib` (see `Langlands/MathlibBase.md`).
