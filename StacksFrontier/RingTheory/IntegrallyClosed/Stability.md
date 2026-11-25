# Finite products of normal rings

Module `StacksFrontier.RingTheory.IntegrallyClosed.Stability`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file proves that normality is preserved by finite products.

## Main results

- `isNormalRing_pi` shows that a product over a finite index type of normal commutative rings is normal. Normality is the predicate `IsNormalRing` of `StacksFrontier.RingTheory.IntegrallyClosed.Defs`: every localization at a prime is an integrally closed domain.

For a prime p of the product, the proof picks an index whose coordinate idempotent lies outside p. Evaluation at that index then induces an isomorphism from the localization of the product at p onto a prime localization of that factor, which is an integrally closed domain.

## References

The product theorem is Tag 0CYA; it uses `IsNormalRing` at each factor, allowing factors with zero divisors. A comment of the file points to the Mathlib instance chain for principal ideal domains corresponding to Tag 00GZ. The module docstrings of the file also describe the normality of regular rings and of integral closures in normal domains; neither result is in the file.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0CYA](https://stacks.math.columbia.edu/tag/0CYA) | `isNormalRing_pi` |  |
| [00GZ](https://stacks.math.columbia.edu/tag/00GZ) | `PrincipalIdealRing.to_uniqueFactorizationMonoid` | a principal ideal domain is a unique factorization domain |
| [00GZ](https://stacks.math.columbia.edu/tag/00GZ) | `UniqueFactorizationMonoid.instIsIntegrallyClosed` | a unique factorization domain is integrally closed in its field of fractions |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/IntegrallyClosed/Stability.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 8 declarations of the source file 3 are kept. The 5 left out are not needed by the results for which the extract is made: `IsRegularRing.isIntegrallyClosed`, `integralClosure_isNormalDomain`, `isIntegrallyClosed_of_isRegularLocalRing`, `localization_of_normal_ring_is_normal`, `main_theorem0567`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
