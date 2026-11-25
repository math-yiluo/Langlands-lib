# Finite prime avoidance

Module `StacksFrontier.RingTheory.Ideal.FinitePrimeAvoidance`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Over a commutative ring, an ideal I that is contained in none of a finite set of prime ideals has an element outside all of them. The theorem `exists_mem_forall_notMem_of_forall_not_le` gives this element directly.

The proof takes the contrapositive of `Ideal.subset_union_prime_finite`. If every element of I lay in the union of the primes, I would lie inside one of the primes.

The table of references cites SGA 3 V 4.1 for this form of prime avoidance.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 3 V 4.1 | `exists_mem_forall_notMem_of_forall_not_le` | more general |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Ideal/FinitePrimeAvoidance.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
