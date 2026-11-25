# Two lemmas on cutting by one element

Module `StacksFrontier.RingTheory.Flat.RegularSequence`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Two lemmas about cutting by one element x of a commutative ring R, in the namespace `Stacks.Flatness.RegularParameters`.

- `rTensor_subtype_span_singleton_injective_of_isSMulRegular`: if x is a nonzerodivisor on an R-module M, the map xR ⊗_R M → R ⊗_R M induced by the inclusion xR ⊆ R is injective. The proof factors multiplication by x on R ⊗_R M ≅ M through the surjection R → xR, r ↦ rx.
- `ofList_map_mk_eq_maximalIdeal`: if R is local and the list x :: rest generates its maximal ideal, then the images of rest generate the maximal ideal of R/xR, which is assumed local as an instance.

The module docstring announces flatness of a finite module from a regular system of parameters whose image stays weakly regular (Tag 07DY); that theorem is not in this file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Flat/RegularSequence.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 8 declarations of the source file 2 are kept. The 6 left out are not needed by the results for which the extract is made: `Module.Flat.of_ofList_eq_maximalIdeal_of_isWeaklyRegular_map`, `Stacks.Flatness.RegularParameters.flat_of_isField`, `Stacks.Flatness.RegularParameters.flat_of_isSMulRegular_of_flat_quotSMulTop`, `Stacks.Flatness.RegularParameters.flat_of_ofList_eq_maximalIdeal_of_isWeaklyRegular`, `Stacks.Flatness.RegularParameters.isLocalHom_of_comp_surjective`, `Stacks.Flatness.RegularParameters.solution`.
- 2 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
