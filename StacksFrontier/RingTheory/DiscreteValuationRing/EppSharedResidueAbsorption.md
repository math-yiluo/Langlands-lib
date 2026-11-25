# Absorbing residue roots in a common base extension

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedResidueAbsorption`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file gives a single weakly unramified base change that supplies deep roots of prescribed residue elements across a finite family. It compares those roots with the original coefficients in any common residue overfield, as needed in the perfect-core branch of Epp’s argument.

`EppCondition.exists_isWeaklyUnramified_forall_exists_pow_eq_of_residueOverfield` takes a discrete valuation ring R, finitely many local R-algebras Sᵢ with local structure maps, and finite sets in the perfect cores of their residue fields, of exponential characteristic p. Given Epp’s condition `h` for every R → Sᵢ and a depth N, it constructs a finite weakly unramified extension R₂ of R with Galois residue extension. In any field receiving the residue fields of Sᵢ and R₂ compatibly over that of R, each selected element from Sᵢ agrees with the pᴺ-th power of an element from the residue field of R₂.

The proof starts with representatives having the same minimal polynomials as the chosen roots. Normality of the new residue extension puts all roots of those polynomials in its image in a common overfield.

The same R₂ serves every index and every compatible overfield. The theorem assumes Epp’s condition on the factors through `h`. Its conclusion supplies the residue input to the Laurent argument, with the equalities interpreted in the overfield.

The comments cite Tag 09F1 and Tag 09F9.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppSharedResidueAbsorption.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 2 declarations of the source file 1 are kept. The 1 left out are not needed by the results for which the extract is made: `Stacks.EppTheorem.EppCondition.exists_isWeaklyUnramified_forall_mem_fieldRange_of_residueOverfield`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
