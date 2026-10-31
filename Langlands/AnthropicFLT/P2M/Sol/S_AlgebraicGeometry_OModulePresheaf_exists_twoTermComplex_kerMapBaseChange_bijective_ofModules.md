# A two-term complex of free modules computing the global sections of a line bundle after any base change (proof)

Module
`Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_twoTermComplex_kerMapBaseChange_bijective_ofModules`.
Its declarations live in the namespace
`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_twoTermComplex_kerMapBaseChange_bijective_ofModules`.

## Statement

`solution`: let `R` be a noetherian ring, `f : X ⟶ Spec R` proper and flat, `M : X.Modules` locally trivial of
rank one (every point has an open neighbourhood `U` with `(Scheme.Modules.pullback U.ι).obj M ≅ 𝒪_U`), and `𝒰`
an ordered affine cover of `X`. Write `F = OModulePresheaf.ofModules f M` and `d₀` for its Čech differential
in degree `0` for `𝒰`. Then there are a two-term complex `G : CoherentBaseChange.TwoTermComplex R` of finitely
generated free `R`-modules (`Def_AlgebraicGeometry_CoherentBaseChange`) and `R`-linear maps `ι0`, `ι1` from
`G` to `d₀`, commuting with the differentials, such that for every `R`-algebra `A` the induced map on kernels
after base change to `A`, `TwoChartCech.kerMapBaseChange G.d d₀ ι0 ι1 comm A`
(`Def_AlgebraicGeometry_TwoChartCech`), is bijective. So `G` computes `H⁰` of `M` universally, as in
Grothendieck's theorem on cohomology and base change. The theorem module
`Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_twoTermComplex_kerMapBaseChange_bijective_ofModules`
states this as `AlgebraicGeometry.OModulePresheaf.exists_twoTermComplex_kerMapBaseChange_bijective_ofModules`
and proves it from `solution`.

## Proof outline

The proof is `main` in the namespace `…P2mGeoMumfordModel`. It applies the algebraic statement
`Module.exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex`
(`Theorems.Thm_Module_exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex`) to the Čech complex
of `F` for `𝒰`, after checking its hypotheses:

- the cochain modules are flat over `R` (`OModulePresheaf.flat_cochain_ofModules_of_locallyTrivial`);
- it is a complex (`OModulePresheaf.d_comp_d`);
- it is bounded: there are no cochains in degrees above the number of opens (`isEmpty_idx`,
  `subsingleton_cochain`);
- its cohomology is finitely generated (`OModulePresheaf.cechFinite_ofModules_of_locallyTrivial`).

As in FLT, the file removes some instances and simp lemmas for the rest of the file (`attribute [-instance]`
and `attribute [-simp]`).

## Provenance and licence

This file is a port of
`P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_twoTermComplex_kerMapBaseChange_bijective_ofModules.lean`
from the Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is licensed
under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in
`licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice applies.
Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech`,
  `Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules`,
  `Definitions.Def_AlgebraicGeometry_TwoChartCech`,
  `Theorems.Thm_Module_exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex`,
  `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_flat_cochain_ofModules_of_locallyTrivial`,
  `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d` and
  `Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_ofModules_of_locallyTrivial` are renamed to the
  corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed; the file used none of its commands.
