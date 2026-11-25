# Comparing module and ring adic completions

Module `StacksFrontier.RingTheory.AdicCompletion.QuotEquivMapPow`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a commutative R-algebra U and an ideal I of the commutative ring R, the I-adic completion of U as an R-module and its IU-adic completion as a ring describe the same inverse limit of R-modules.

`adicCompletionLinearEquivMap` gives the R-linear isomorphism between the completions. It applies the levelwise equivalence `quotEquivMapPow` to every coordinate. The accompanying lemmas show that at level n this equivalence sends the class of x modulo IⁿU to the class of the same x modulo (IU)ⁿ and commutes with the reduction maps.

The proof applies the equivalences to sequences of residue classes. Compatibility with reduction and injectivity of each levelwise map identify the two conditions for a sequence to be coherent.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/AdicCompletion/QuotEquivMapPow.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
