# Functoriality of reduced tensor products

Module `StacksFrontier.RingTheory.DiscreteValuationRing.ReducedTensorTower`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file constructs the maps on reductions used to compare reduced tensor products of commutative algebras over a common commutative ring R.

`ReducedTensorTower.Reduction` is the quotient by the nilradical. An R-algebra homomorphism induces `reductionMap`, and an R-algebra equivalence induces `reductionEquiv`. The lemma `reductionMap_comp` shows that reduction respects composition. Given maps f and g on the two factors, `reducedTensorMap` sends the class of a ⊗ c to the class of f(a) ⊗ g(c) (`reducedTensorMap_tmul`).

The constructions descend the algebra maps to quotients because homomorphisms preserve nilpotents and equivalences carry nilradicals onto nilradicals. The identities can be checked on representatives.

The maps compare the reductions of two tensor products. Using reduction through an additional tensor step calls for a separate compatibility result, particularly in inseparable, nonexcellent settings.

The module docstring also lists the identity law for `reductionMap` among the results; the file does not contain it. The namespace `IsDiscreteValuationRing.ReducedTensorTower` at the end of the file is empty.

The cited applications are the reduced composita in Tag 09EQ, Tag 0GLR and Tag 09II.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/ReducedTensorTower.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 11 declarations of the source file 8 are kept. The 3 left out are not needed by the results for which the extract is made: `ReducedTensorTower.reducedTensorMap_includeLeft`, `ReducedTensorTower.reducedTensorMap_includeRight`, `ReducedTensorTower.reductionMap_id`.
- 1 command that is not a declaration is left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
