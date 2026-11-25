# Product of the residue fields at the minimal primes

Module `StacksFrontier.RingTheory.MinimalPrimes.Localization`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a commutative ring A, `minimalPrimes.residueFieldProduct A` is the product ∏ κ(q) of the residue fields `Ideal.ResidueField q` over the minimal primes q of A, written as an `abbrev` for a dependent function type on the subtype `minimalPrimes A`. The instance `minimalPrimes.isPrime_coe` records that a minimal prime, seen as an ideal, is prime, which the residue fields need.

The module docstring still announces the contraction correspondence between the minimal primes of a localization of R at a prime p and the minimal primes of R contained in p, a comparison map of residue-field products and its localization theorem (Tag 0C3B); none of them is in the file, whose sections `Comparison` and `Localization` hold only variable declarations.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/MinimalPrimes/Localization.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 16 declarations of the source file 2 are kept. The 14 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- 11 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
