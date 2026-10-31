# Line bundles on a proper scheme over a noetherian ring have finite Čech cohomology (proof)

Module
`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial`.
Its only declaration is
`P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial.solution`.

## Statement

`solution`: let `R` be a noetherian ring, `π : V ⟶ Spec R` proper and `M : V.Modules` a sheaf of modules that
is locally trivial of rank one: every point has an open neighbourhood `U` with
`(Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit _`. Then for every ordered affine cover `K` of `V`,
the presheaf of modules `OModulePresheaf.ofModules π M` (`Def_AlgebraicGeometry_OModulePresheafOfModules`) has
finitely generated Čech cohomology for `K` in every degree. The theorem module
`Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial` states this as
`AlgebraicGeometry.OModulePresheaf.cechFinite_ofModules_of_locallyTrivial` and proves it from `solution`.

## Proof outline

`OModulePresheaf.ofModules π M` is coherent and quasi-coherent by
`OModulePresheaf.isCoherent_ofModules_of_locallyTrivial` and
`OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial` (from the corresponding theorem modules), so
`OModulePresheaf.cechFinite_of_isProper` applies.

As in FLT, the file removes some instances and simp lemmas for the rest of the file (`attribute [-instance]`
and `attribute [-simp]`).

## Provenance and licence

This file is a port of
`P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial.lean` from the Anthropic
Lean formalization of Fermat's Last Theorem at commit `6e837e75355538c7f80bab5b956861e86c4eacc2` (registered
literature `anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in
`licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice applies.
Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules`,
  `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial`,
  `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_ofModules_of_locallyTrivial` and
  `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_of_isProper` are renamed to the corresponding
  `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed; the file used none of its commands.
