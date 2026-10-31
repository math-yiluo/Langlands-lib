# Čech cochains of a locally trivial sheaf over a flat separated base are flat (proof)

Module `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_flat_cochain_ofModules_of_locallyTrivial`.
Its declarations live in the namespace
`P2MW.S_AlgebraicGeometry_OModulePresheaf_flat_cochain_ofModules_of_locallyTrivial`.

## Statement

`solution`: let `R` be a commutative ring, `π : V ⟶ Spec R` flat and separated, and `M` a sheaf of
modules on `V` that is locally isomorphic to the structure sheaf (every point has an open neighbourhood
`U` with `M|_U ≅ 𝒪_U`). Then for every ordered affine cover `K` of `V` and every `i`, the module of Čech
`i`-cochains of `OModulePresheaf.ofModules π M` for `K` is flat over `R`. The theorem module
`Theorems.Thm_AlgebraicGeometry_OModulePresheaf_flat_cochain_ofModules_of_locallyTrivial` states this as
`AlgebraicGeometry.OModulePresheaf.flat_cochain_ofModules_of_locallyTrivial` and proves it from
`solution`.

## Proof outline

1. `CechFlatSol.isAffineOpen_inter`: on a separated scheme every intersection `K.inter s` is affine
   (induction on the length of `s`, using that intersections of affine opens in a separated scheme are
   affine). `V` is separated because `π` is.
2. For each index `s`, put `W = K.inter s`. `Γ(V, W)` is flat over `R`
   (`Scheme.TwoAffineOpenCover.flat_sections_of_flat`, since `π` is flat and `W` is affine), and `Γ(M, W)`
   is a projective, hence flat, `Γ(V, W)`-module
   (`Scheme.Modules.projective_sections_of_locallyTrivial`). By transitivity of flatness `Γ(M, W)` is
   flat over `R`.
3. The cochain module is the finite product of these modules, isomorphic to their direct sum, and a
   finite direct sum of flat modules is flat.

## Provenance and licence

This file is a port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_flat_cochain_ofModules_of_locallyTrivial.lean`
from the Anthropic Lean formalization of Fermat's Last Theorem at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2` (registered literature
`anthropic-flt-complete-lean-source-6e837e75`). That work is Copyright 2026 Anthropic, PBC, and is
licensed under the Apache License, Version 2.0. Copies of its `LICENSE`, `NOTICE` and `ATTRIBUTION.md`
are in `licenses/Anthropic-FLT/`. `ATTRIBUTION.md` has no row for this file, so no third-party notice
applies. Declaration names and namespaces are FLT's. The port makes only these changes:

- an attribution header is added above the imports;
- the imports of the FLT modules `Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech`,
  `Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules`,
  `Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_sections_of_flat` and
  `Theorems.Thm_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial` are renamed to the
  corresponding `Langlands.AnthropicFLT.*` modules;
- FLT's lakefile options are set after the imports: `maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000` and `backward.isDefEq.respectTransparency.types false`;
- the import of FLT's helper module `P2M.Util` is removed; the file used none of its commands. No
  declaration, statement or proof step changed.
