# Normality of polynomial rings

Module `StacksFrontier.RingTheory.IntegrallyClosed.Polynomial`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file proves that the polynomial ring in one variable over a normal commutative ring is normal. The theorem `polynomial_ring_normal` takes `IsNormalRing R` and gives `IsNormalRing (Polynomial R)`, where normality requires every prime localization to be an integrally closed domain.

For a prime q of R[X], contract it to p in R and first invert the constant polynomials from the complement of p. This gives the polynomial ring over the normal domain R localized at p. The localization at q is a further localization of that integrally closed domain, so it is again an integrally closed domain.

The theorem applies to normal rings, including those with zero divisors. It is Tag 00H1 and uses Mathlib's normal-domain polynomial case, Tag 030A.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00H1](https://stacks.math.columbia.edu/tag/00H1) | `polynomial_ring_normal` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/IntegrallyClosed/Polynomial.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
