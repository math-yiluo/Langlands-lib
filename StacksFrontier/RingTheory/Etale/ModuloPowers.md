# Congruence modulo the maximal ideal from a surjective residue map

Module `StacksFrontier.RingTheory.Etale.ModuloPowers`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

`Stacks.Etale.PrincipalPowerIso.exists_sub_mem_maximalIdeal_of_surjective_residue_comp` takes a ring homomorphism F : A → B into a local ring B whose composite with the residue map of B is surjective. It gives, for every b in B, an a in A with b − F(a) in the maximal ideal of B. Only the target need be local, and F need not be a local homomorphism. The proof lifts the residue class of b.

The two module docstrings still state Tag 0GSD, that an étale local map with surjective residue field map is bijective modulo every power of a suitable element of the maximal ideal, with its proof by Newton's method and its implementation notes; the file contains neither that theorem nor its proof, and its remaining sections are empty.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Etale/ModuloPowers.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 14 declarations of the source file 1 are kept. The 13 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- 1 command that is not a declaration is left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
