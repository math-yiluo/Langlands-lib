# Maps induced on adic completions

Module `StacksFrontier.RingTheory.AdicCompletion.CompletionMap`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

An algebra map A → B induces an algebra map between adic completions.

For an A-algebra B and ideal I of A, `AdicCompletion.completionMap` is the A-algebra map from the I-adic completion of A to the IB-adic completion of B, where IB is the extended ideal. It lifts the level maps `AdicCompletion.completionLevel`, evaluation at level n followed by the quotient map A/Iⁿ → B/(IB)ⁿ, which the lemma `AdicCompletion.factor_completionLevel` shows compatible with the transition maps. The lemma `AdicCompletion.evalₐ_completionMap` sends a representative a at level n to the residue of its image in B modulo (IB)ⁿ, and `AdicCompletion.val_completionMap` says the same for the underlying compatible family.

The module docstring also announces the induced ring homomorphism for an arbitrary ring map carrying one ideal into another, and the file ends with a section heading for it; that map is not in the file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/AdicCompletion/CompletionMap.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 9 declarations of the source file 5 are kept. The 4 left out are not needed by the results for which the extract is made: `AdicCompletion.completionMap_algebraMap`, `adicCompletionMap`, `adicCompletionMap_comp_algebraMap`, `adicCompletionMap_evalₐ`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
