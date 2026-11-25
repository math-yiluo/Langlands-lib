# Elements in every minimal prime of a reduced ring

Module `StacksFrontier.RingTheory.Flat.ReducedFibres`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

In a reduced commutative ring R, an element lying in every minimal prime of R is zero: this is `Stacks.Flatness.ReducedFibreAscent.eq_zero_of_forall_mem_minimalPrimes`. The proof identifies the intersection of the minimal primes with the radical of the zero ideal, which is zero because R is reduced.

The module docstring describes the ascent of reducedness along a flat map of Noetherian rings with reduced fibres (Tag 0C21) and lists three main results for it; none of them is in this file, which holds only the lemma above.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Flat/ReducedFibres.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 6 declarations of the source file 1 are kept. The 5 left out are not needed by the results for which the extract is made: `Stacks.Flatness.ReducedFibreAscent.isReduced_left_of_tensor`, `Stacks.Flatness.ReducedFibreAscent.isReduced_of_flat_of_forall_isReduced_fiber`, `Stacks.Flatness.ReducedFibreAscent.isReduced_tensorProduct_pi`, `Stacks.Flatness.ReducedFibreAscent.solution`, `isReduced_of_flat_of_isReduced_fiber`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- The 2 references to EGA and SGA that the source writes as attributes of that library belong to declarations left out; none is in this file.
