# Forgetting the module structure preserves finite colimits of sheaves

Module `StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a sheaf of rings R on the open-cover site of a topological space X, the instance `toSheafPFC` says that the forgetful functor `SheafOfModules.toSheaf R`, from sheaves of R-modules to sheaves of abelian groups, preserves finite colimits. Both categories compute colimits by sheafifying presheaf colimits. Sheafification of presheaves of modules is a left adjoint whose counit is an isomorphism, and followed by the forgetful functor it is isomorphic to forgetting to presheaves of abelian groups and then sheafifying, a composite of two functors that preserve finite colimits.

The transfer step is the general lemma `preservesColim_comp_transfer`: if G preserves the colimit of a diagram E and G ⋙ F does too, then F preserves the colimit of E ⋙ G.

The instance is stated under the file's standing hypotheses: abelian-group sheafification on the open-cover site, the characterization of sheafification equivalences by local bijectivity, and enough injectives for module sheaves. The module docstring describes cohomology groups Hⁿ(U, F), their restriction maps and the vanishing of a positive-degree class on an open covering (Tag 01E3); none of this is in the file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Topology/Sheaves/Cohomology/Locality/CohomologyVanishesLocally.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 18 declarations of the source file 2 are kept. The 16 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- 3 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
