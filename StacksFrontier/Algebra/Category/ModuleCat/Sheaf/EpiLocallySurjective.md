# Epimorphisms of sheaves of modules are locally surjective

Module `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let `R` be a sheaf of rings on a site `(C, J)`.

## Main results

- `isLocallySurjective_of_epi`: for an epimorphism `f : M ⟶ N` of sheaves of `R`-modules, the underlying morphism of presheaves of abelian groups is locally surjective.
- `imageSieve_mem_of_epi`: hence the sieve of arrows along which a section `s` of `N` over `V` restricts into the image of `f` covers `V`.

`counitApp` is the counit of the sheafification adjunction for presheaves of modules at a sheaf of modules, an isomorphism.

## Proof

The image of `f` is taken in the abelian category of presheaves of modules. Sheafifying the inclusion of that image gives an isomorphism (`isIsoSheafificationMapImageι`), so the inclusion is locally surjective; the map onto the image is surjective on sections, and the composite is locally surjective.

## Points to watch

`J` must have sheafification of abelian groups in the module universe `t`, with weak equivalences the locally bijective maps; `t` is independent of the universe `u` of the rings. The module docstring also announces the converse, which the file does not contain.

## References

Tag 01AH.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/EpiLocallySurjective.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 11 declarations of the source file 6 are kept. The 5 left out are not needed by the results for which the extract is made: `Stacks.SheafOfModules.EpiMono.epi_iff_isLocallySurjective`, `Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective`, `Stacks.SheafOfModules.EpiMono.epi_toSheaf_map`, `Stacks.SheafOfModules.EpiMono.exists_covering_of_epi`, `Stacks.SheafOfModules.EpiMono.preservesEpimorphismsToSheaf`.
- 1 command that is not a declaration is left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
