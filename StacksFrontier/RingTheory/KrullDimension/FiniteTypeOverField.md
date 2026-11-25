# Dimension and maximal chains over a field

Module `StacksFrontier.RingTheory.KrullDimension.FiniteTypeOverField`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a finite-type domain over a field, the transcendence degree of its fraction field controls both its Krull dimension and the lengths of maximal chains of primes.

`ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg` takes a finite-type domain S over a field k with fraction field K. It identifies dim S and dim A with the transcendence degree of K over k whenever A is a localization of S at a maximal ideal. Both K and A are specified by localization typeclasses, and the comparison uses `Cardinal.toENat` to express the transcendence degree in the dimension type.

`Algebra.FiniteType.ringKrullDim_eq_height_of_isMaximal_and_length_eq_ringKrullDim` proves that each maximal ideal has height dim S and that every maximal chain has length dim S under the same hypotheses on k and S. The chain is a `RelSeries` of covering pairs with a minimal first prime and a maximal last prime. Its length counts strict inclusions, and the minimal first prime is zero because S is a domain.

Noether normalization provides a finite injective map from a polynomial ring in dim S variables to S. Algebraicity then computes the transcendence degree, and going-down lifts the height of a contracted maximal ideal of the polynomial ring. For the chain result, contraction along a polynomial presentation embeds the spectrum of S into that of the polynomial ring and preserves covering pairs. The height formula for covering chains in a regular ring gives the length after cancelling the height of the kernel.

The transcendence-degree and maximal-chain theorems are Tag 00P0 and Tag 00OS. The arguments use Tag 00OY, Tag 030H, Tag 00ON and Tag 00OR. The transcendence-degree theorem is a special case of EGA IV 5.5.8.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00P0](https://stacks.math.columbia.edu/tag/00P0) | `ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg` | The transcendence degree is compared through `Cardinal.toENat`, the field of fractions is an abstract `IsFractionRing` and the local ring an abstract `IsLocalization.AtPrime`. See the module docstring. |
| [00OS](https://stacks.math.columbia.edu/tag/00OS) | `ringKrullDim_eq_height_of_isMaximal_and_length_eq_ringKrullDim` | `dim(S_𝔪)` is written `𝔪.height`, the Krull dimension of any model of the local ring at `𝔪`; the source's \"in words\" clause is kept as a second conjunct, a maximal chain of primes being a `RelSeries` for the covering relation `⋖` on `PrimeSpectrum S` whose head is minimal and whose last is maximal. See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 5.5.8 | `ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/KrullDimension/FiniteTypeOverField.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
