# Openness of the normal locus of a Noetherian domain

Module `StacksFrontier.RingTheory.NormalLocus.Open`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The normal locus of a domain is the set of primes at which its local ring is integrally closed. This file proves openness when the locus contains a nonempty principal open given by a normal localization.

`PrimeSpectrum.isOpen_setOf_isIntegrallyClosed_atPrime` takes a Noetherian domain R and an element f, with `hf : f ≠ 0` and `hf'` asserting integral closedness of `Localization.Away f`. It proves that the set of primes p with `IsIntegrallyClosed (Localization.AtPrime p.asIdeal)` is open. Each such localization is a domain by the hypotheses on R.

Integral closedness persists when passing to a smaller prime, and all primes outside V(f) are in the normal locus. The proof places every prime minimal among those outside the normal locus among the associated primes of R/fR. Locally at such a prime, it picks an integral fraction outside the local ring and rescales it so that f belongs to its denominator ideal while the fraction stays outside the ring. The denominators then annihilate a nonzero class modulo f. Prime avoidance gives the associated-prime statement at the local ring, and clearing denominators descends it to R. Finiteness of associated primes makes the complement a finite union of closed sets.

With another model for localization away from f, transport integral closedness to `Localization.Away f` along a localization equivalence.

Stacks Project Tag 0332, with Tag 00LC for finiteness of associated primes, Tag 00LL for prime avoidance, and Tag 058A for the description via annihilators.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0332](https://stacks.math.columbia.edu/tag/0332) | `PrimeSpectrum.isOpen_setOf_isIntegrallyClosed_atPrime` | Normality of a localization is spelled `IsIntegrallyClosed`, Mathlib having no \   predicate for a normal ring; the `IsDomain` conjunct of the spelling used for tags 030C (1) \   and 031S is automatic here because `R` is a domain. `R_f` is the canonical model \   `Localization.Away f`. See the module docstring. |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/NormalLocus/Open.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
