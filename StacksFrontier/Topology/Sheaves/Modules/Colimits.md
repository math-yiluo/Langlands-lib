# The stalk functor on sheaves of modules

Module `StacksFrontier.Topology.Sheaves.Modules.Colimits`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a sheaf of rings O on the open-cover site of a topological space X and a point x ∈ X, the stalk of a sheaf of O-modules is a module over the stalk ring Oₓ, functorially.

In `AlgebraicGeometry.SheafOfModules`, `stalkObj` bundles the stalk of the underlying abelian sheaf as an Oₓ-module. `stalkMap` is the induced linear map, with scalar compatibility checked by representing both the scalar and the module element on a common neighborhood. These form `stalkFunctor`. The lemma `germ_hom_smul` is Mathlib's germ formula for the scalar action, germ(r • m) = germ r • germ m, written with the germ maps as bundled morphisms of abelian groups and of rings; it holds for any presheaf of modules.

The space, rings and modules are in the same universe. The module docstring describes colimits of sheaves of modules computed by sheafification, the preservation of colimits by the stalk functor, and element-level forms of it for ℕ-indexed colimits; none of these is in the file.

The file refers to Tag 01AH; the existence of colimits of sheaves of modules is the Mathlib instance listed below.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [01AH](https://stacks.math.columbia.edu/tag/01AH) | `SheafOfModules.instHasColimitsOfSizeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf` | colimits_exist |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Topology/Sheaves/Modules/Colimits.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 13 declarations of the source file 4 are kept. The 9 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.SheafOfModules.colimitSheafificationCocone`, `AlgebraicGeometry.SheafOfModules.exists_map_eq_zero_of_stalkMap_eq_zero`, `AlgebraicGeometry.SheafOfModules.exists_stalkMap_eq`, `AlgebraicGeometry.SheafOfModules.isColimitMapCoconeOfSequence`, `AlgebraicGeometry.SheafOfModules.isColimit_colimitSheafificationCocone`, `AlgebraicGeometry.SheafOfModules.preservesColimit_comp_stalkFunctor_forget`, `AlgebraicGeometry.SheafOfModules.preservesColimitsOfSize_sheafification`, `AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits`, `AlgebraicGeometry.SheafOfModules.toSheaf_preservesColimits`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
