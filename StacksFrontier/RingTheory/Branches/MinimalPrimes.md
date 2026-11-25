# Minimal primes of the reduction of a ring

Module `StacksFrontier.RingTheory.Branches.MinimalPrimes`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

`finite_minimalPrimes_quotient_nilradical` shows that if a commutative ring A has finitely many minimal primes, then so does its reduction A ⧸ nilradical A. Contraction along the quotient map is injective on ideals and carries the minimal primes of the reduction onto those of A.

The module docstring describes correspondences between minimal and maximal primes under base change, and normality results, used to compute the branches of a local ring, and lists five main results on them; none of these is in the file, whose only declaration is the lemma above.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Branches/MinimalPrimes.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 23 declarations of the source file 1 are kept. The 22 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- 4 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
