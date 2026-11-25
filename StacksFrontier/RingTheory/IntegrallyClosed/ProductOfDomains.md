# Normality and decomposition by minimal primes

Module `StacksFrontier.RingTheory.IntegrallyClosed.ProductOfDomains`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a reduced commutative ring with finitely many minimal primes, this file relates normality to integral closedness in the total ring of fractions and to decomposition into normal domains.

`isIntegrallyClosed_tfae_of_finite_minimalPrimes` proves four equivalent conditions for such a ring R.

1. Every prime localization of R is an integrally closed domain.
2. R is integrally closed in its total ring of fractions.
3. R is isomorphic to a finite product of integrally closed domains.
4. The canonical map to the product of the quotients R/p by the minimal primes is bijective, and every quotient is integrally closed.

The supporting instance `isFractionRing_pi` identifies the product of total rings of fractions as a total ring of fractions of the product, allowing an arbitrary index type. The theorem `isIntegrallyClosed_pi_iff` tests integral closedness in a finite product of commutative rings factor by factor.

The decomposition proof first expresses the total ring of fractions as the product of localizations at the minimal primes. The coordinate idempotents are integral, so integral closedness puts them in R. Their components show that distinct minimal primes are comaximal, and the Chinese remainder theorem gives the quotient decomposition. Reducedness ensures injectivity, and the product criterion gives integral closedness of each factor.

In the third condition the factors live in the same universe as R. The fourth condition records the specific quotient maps and the factors produced by the proof.

The equivalence is Tag 030C. The total-fraction-ring argument uses Tag 02LX, with the zerodivisor description from Tag 00EW, and the factorwise criterion uses Tag 0CY9. The table of references cites EGA IV 5.13.5 for decomposition in the Noetherian case and EGA IV 6.14.1.1 for the implication from normality to integral closedness.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [030C](https://stacks.math.columbia.edu/tag/030C) | `isIntegrallyClosed_tfae_of_finite_minimalPrimes` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 5.13.5 | `isIntegrallyClosed_tfae_of_finite_minimalPrimes` | Noeth ⇒ product of doms |
| EGA | IV 6.14.1.1 | `isIntegrallyClosed_tfae_of_finite_minimalPrimes` | (i) |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/IntegrallyClosed/ProductOfDomains.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
