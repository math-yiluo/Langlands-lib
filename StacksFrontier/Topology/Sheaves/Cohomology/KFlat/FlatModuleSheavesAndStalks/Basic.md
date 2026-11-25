# The structure sheaf of a ringed space as a sheaf of rings

Module `StacksFrontier.Topology.Sheaves.Cohomology.KFlat.FlatModuleSheavesAndStalks.Basic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a ringed space X, `OXModule.ringSheaf` views the structure sheaf O_X, a sheaf of commutative rings, as a sheaf of rings on the Grothendieck topology of open covers of X; forgetting commutativity preserves the sheaf condition.

For a presheaf of modules M over `OXModule.ringSheaf X`, three local instances supply the module structures used with it: `OXModule.sectionModule` and `OXModule.sectionPresheafModule` make the sections over an open U, read in M and in its underlying presheaf of abelian groups, modules over O_X(U), and `OXModule.stalkModule` makes the stalk Mₓ a module over the stalk ring O_{X,x}. Being local, they act as instances only inside this file. The space, rings and modules use one universe.

The module docstring and the long comment after it describe a category of O_X-modules, its tensor product, flatness, stalkwise Tor₁ and the comparison of stalks; none of this is in the file.

The structure sheaf as a sheaf of rings is EGA 0 4.1.1.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 4.1.1 | `ringSheaf` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Topology/Sheaves/Cohomology/KFlat/FlatModuleSheavesAndStalks/Basic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 36 declarations of the source file 4 are kept. The 32 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
