# The two stalks of a presheaf of commutative rings

Module `StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a presheaf R of commutative rings on a topological space X and a point x, the stalk of R can be taken in `CommRingCat` or, after forgetting commutativity, in `RingCat`. `SemilinearStalk.commStalkIso` is the comparison isomorphism in `RingCat` between the stalk of `R ⋙ forget₂ CommRingCat RingCat` and the commutative stalk viewed as a ring; it comes from the preservation, by the forgetful functor, of the filtered colimit computing the stalk. `SemilinearStalk.commStalkRingEquiv` is the same comparison as a ring equivalence, and `SemilinearStalk.commStalkRingEquiv_germ` says that it sends the germ of a section r over an open U ∋ x to the germ of r.

The space and the rings share one universe. The module docstring and the section headers announce semilinearity results for stalk maps of presheaves of modules and for the stalks of pullbacks and inverse images, and the agreement of the two module actions on a stalk; none of these is in the file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Topology/Sheaves/Functors/Module/SemilinearStalk.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 27 declarations of the source file 3 are kept. The 24 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- 2 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
