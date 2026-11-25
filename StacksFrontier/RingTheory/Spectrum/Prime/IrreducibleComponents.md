# Irreducible components through a prime

Module `StacksFrontier.RingTheory.Spectrum.Prime.IrreducibleComponents`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Irreducible components of a spectrum through a point correspond to minimal primes of the local ring at that point.

The declarations in `PrimeSpectrum` work for a commutative semiring R, a prime p and any commutative semiring S realizing the localization at p. `pt` is the spectrum point of p. `irreducibleComponentsThrough` is the set of irreducible components containing that point, and `irreducibleComponentsThroughEquiv` gives a bijection from it to minimal primes of S.

It composes the correspondence between minimal primes of R inside p and their zero loci, maximal among irreducible closed sets by reversal of inclusion, with the localization correspondence for minimal primes. The simplification lemmas compute the forward map by extending the vanishing ideal and the inverse map by taking the zero locus of the contraction.

## References

Tag 00ET part (2). The references include EGA I 1.1.1 for spectrum points, EGA I 1.1.14 for minimal primes and components, SGA 1 IV 2.5 for localization and EGA IV 5.1.12 for the component correspondence as a special case.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00ET](https://stacks.math.columbia.edu/tag/00ET) | `irreducibleComponentsThroughEquiv` | (2) |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | I 1.1.1 | `pt` |  |
| EGA | I 1.1.14 | `minimalPrimesBelowEquivIrreducibleComponentsThrough` | (i) |
| SGA | 1 IV 2.5 | `minimalPrimesLocalizationEquivMinimalPrimesBelow` | localization at a prime |
| EGA | IV 5.1.12 | `irreducibleComponentsThroughEquiv` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Spectrum/Prime/IrreducibleComponents.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 12 declarations of the source file 7 are kept. The 5 left out are not needed by the results for which the extract is made: `PrimeSpectrum.coe_irreducibleClosedThroughEquiv`, `PrimeSpectrum.coe_irreducibleClosedThroughEquiv_symm`, `PrimeSpectrum.irreducibleClosedThrough`, `PrimeSpectrum.irreducibleClosedThroughEquiv`, `PrimeSpectrum.primesBelowEquivIrreducibleClosedThrough`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 4 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
