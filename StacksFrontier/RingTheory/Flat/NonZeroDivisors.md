# Nonzerodivisors in flat algebras

Module `StacksFrontier.RingTheory.Flat.NonZeroDivisors`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A nonzerodivisor remains a nonzerodivisor under a flat map of commutative rings.

For a flat A-algebra B, `algebraMap_mem_nonZeroDivisors_of_flat` sends any a in the submonoid of nonzerodivisors of A to a nonzerodivisor of B. The proof applies Mathlib’s `Module.Flat.isSMulRegular_of_nonZeroDivisors` to B as an A-module and identifies scalar multiplication by a with multiplication by its image in B.

This is the algebra case of preservation of injective scalar multiplication on a flat module. References are EGA 0 6.3.4, IV 20.6.9 and IV 21.15.7, and SGA 1 IV 1.3 and 3 VIB 12.8.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 6.3.4 | `algebraMap_mem_nonZeroDivisors_of_flat` | M = B |
| EGA | IV 20.6.9 | `algebraMap_mem_nonZeroDivisors_of_flat` | partial |
| EGA | IV 21.15.7 | `algebraMap_mem_nonZeroDivisors_of_flat` | special case |
| SGA | 1 IV 1.3 | `algebraMap_mem_nonZeroDivisors_of_flat` | special case |
| SGA | 3 VIB 12.8 | `algebraMap_mem_nonZeroDivisors_of_flat` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Flat/NonZeroDivisors.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 5 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
