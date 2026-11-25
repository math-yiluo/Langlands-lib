# Finite closed subsets of prime spectra

Module `StacksFrontier.RingTheory.DedekindDomain.ClosedSubsetFinite`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file proves finiteness of proper Zariski-closed subsets for Noetherian rings satisfying `Ring.DimensionLEOne`, including Dedekind domains.

`PrimeSpectrum.finite_zeroLocus` says that the vanishing locus of every nonzero ideal is finite. `PrimeSpectrum.finite_of_isClosed_of_ne_univ` gives the corresponding result for any proper closed subset. For Dedekind domains the file records the second, as `IsDedekindDomain.finite_of_isClosed_of_ne_univ`.

The proof uses `Ideal.isMinimalPrime_of_ne_bot`. When every nonzero prime is maximal, a prime containing a nonzero ideal is minimal over it. Noetherianity gives finiteness of those minimal primes. A proper closed set can be written as the vanishing locus of an ideal, and properness forces that ideal to be nonzero.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DedekindDomain/ClosedSubsetFinite.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 5 declarations of the source file 4 are kept. The 1 left out are not needed by the results for which the extract is made: `IsDedekindDomain.finite_zeroLocus`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
