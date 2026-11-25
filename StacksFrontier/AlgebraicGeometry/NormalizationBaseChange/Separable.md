# Normality of the integral closure in the total ring of fractions

Module `StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Separable`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file proves that the integral closure of a reduced ring in its total ring of fractions is normal when the ring has finitely many minimal primes.

`isIntegrallyClosed_integralClosure_of_isDomain` shows that the integral closure of a domain R
in its fraction field F is integrally closed.

`isNormalRing_integralClosure_fractionRing_of_finite_minimalPrimes` shows that the
integral closure A′ in the total ring of fractions of a reduced ring A with finitely
many minimal primes is normal.

The proof splits A′ into the integral closures of the minimal-prime quotients, Tag 035P,
and applies the domain case to each factor.

The module docstring also announces normality after a separable extension of the ground field
and the preservation of non-zerodivisors under extension of the ground field; they are not in
this file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/NormalizationBaseChange/Separable.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 5 declarations of the source file 2 are kept. The 3 left out are not needed by the results for which the extract is made: `IsNormalRing.tensorProduct_of_isSeparableExtension`, `includeRight_mem_nonZeroDivisors_tensorProduct`, `isNormalRing_tensorProduct_integralClosure_fractionRing`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
