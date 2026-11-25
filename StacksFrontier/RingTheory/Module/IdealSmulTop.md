# Ideal multiplication on the ring

Module `StacksFrontier.RingTheory.Module.IdealSmulTop`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Multiplying the whole ring, viewed as a module over itself, by an ideal recovers that ideal.

`Ideal.smul_top_eq_self` proves I • ⊤ = I for any ideal I of a commutative ring R, with ⊤ taken in the submodules of R. The proof rewrites the ideal action as ideal multiplication using `Ideal.smul_eq_mul` and applies `Ideal.mul_top`.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Module/IdealSmulTop.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
