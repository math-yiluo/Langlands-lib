# Adic completeness along a nilpotent ideal

Module `StacksFrontier.RingTheory.AdicCompletion.LiftToComplete`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A commutative ring is adically complete along a nilpotent ideal.

`IsAdicComplete.of_isNilpotent` takes an ideal I of R with Iᵏ = 0 for some k and proves `IsAdicComplete I R`. The filtration is eventually zero, so the ring is separated, and an adic Cauchy sequence converges to its k-th term.

The module docstring also announces the extension of an algebra map into a complete ring across the completion of its source, the uniqueness of that extension and the compatibility of the projections of a completion; none of these is in the file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/AdicCompletion/LiftToComplete.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 6 declarations of the source file 1 are kept. The 5 left out are not needed by the results for which the extract is made: `AdicCompletion.algHom_ext_of_isHausdorff`, `AdicCompletion.eq_of_sub_mem_pow`, `AdicCompletion.exists_algHom_of_isAdicComplete`, `AdicCompletion.factorₐ_evalₐ`, `AdicCompletion.factorₐ_mk`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
