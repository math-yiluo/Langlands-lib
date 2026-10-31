# A locally trivial sheaf of modules gives a quasi-coherent presheaf (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial`.
Its declarations live in the namespace
`P2MW.S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial`.

## Statement

`solution`: let `R` be a commutative ring, `π : V ⟶ Spec R`, and `M` a sheaf of modules on `V` such that
every point has an open neighbourhood `U` with `M|_U` isomorphic to the structure sheaf of `U`. Then the
presheaf of modules `OModulePresheaf.ofModules π M` is quasi-coherent in the sense of
`OModulePresheaf.IsQuasicoherent`: on every affine open `U` and for every `f ∈ Γ(V, U)`, the sections over
`D(f)` are the localization of the sections over `U` at `f`. The theorem module
`Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial` states this
as `AlgebraicGeometry.OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial` and proves it from
`solution`.

## Proof outline

For an affine open `U` and `f ∈ Γ(V, U)`, the two conditions of `IsQuasicoherent` are exactly the
conclusion of the FLT theorem `Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial` for `M`, `U`
and `f`. The proof applies it.

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial.lean`
from the Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules` and
  `Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial` are renamed to
  the corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed; the file used none of its commands. No
  declaration, statement or proof step changed.
