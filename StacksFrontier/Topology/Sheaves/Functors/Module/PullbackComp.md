# Pushforward of sheaves of modules preserves zero morphisms

Module `StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

`RingedSpaceModuleAdjunction.modulePushforward_map_zero`: for a morphism f : X ⟶ Y of ringed spaces and sheaves of modules F and G over the structure sheaf of X, the pushforward `RingedSpaceModuleAdjunction.modulePushforward f` sends the zero morphism F ⟶ G to the zero morphism. It holds by `rfl`, since the pushforward does not change the maps on sections, only the opens indexing them, and it is a simp lemma. The pushforward is defined in `StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace`. The ringed spaces, structure rings and module sheaves share one universe.

The module docstring describes the composition and unit laws for pullback and pushforward (Tag 0096) and the structure-sheaf map of a morphism as a map of module sheaves; none of these is in the file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Topology/Sheaves/Functors/Module/PullbackComp.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 16 declarations of the source file 1 are kept. The 15 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
