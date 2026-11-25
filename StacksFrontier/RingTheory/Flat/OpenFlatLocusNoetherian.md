# Openness of the flat locus over a polynomial ring

Module `StacksFrontier.RingTheory.Flat.OpenFlatLocusNoetherian`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let R be a Noetherian commutative ring, P the polynomial ring over R in n variables, and M a finitely presented P-module. The file proves that relative flatness of M over R spreads from the localization at a prime of P to a basic open neighbourhood.

## Main results

- `exists_away_flat_of_flat_atPrime_mvPolynomial_of_isNoetherianRing` finds g outside a prime 𝔮 of P such that M localized by inverting g is R-flat, given that M localized at 𝔮 is R-flat.
- `isOpen_setOf_flat_localizedModule_atPrime_mvPolynomial` deduces that the set of such primes 𝔮 is open in Spec(P).
- For any R-algebra S, `flat_localizedModule_away_of_forall_flat_atPrime` deduces R-flatness after inverting g from R-flatness of the stalks at every prime in the basic open of g.

`FreeComplexTruncation.truncRank` and `FreeComplexTruncation.truncD` give the ranks and coordinate differentials of a free complex cut off at a chosen degree, with a new free term attached at the top. The differentials are composed with `LinearMap.clampFin`, which maps `Fin a → S` to `Fin b → S` by restricting coordinates or extending them by zero; when a = b, `LinearMap.clampFinEquiv` is the resulting isomorphism. `TruncFibreExact` requires injectivity at the top and exactness through degree one after tensoring with S_𝔮/𝔭S_𝔮, where 𝔭 is the contraction of 𝔮.

The proof uses regularity and the dimension bound of polynomial fibres to make a high syzygy free at 𝔮, then clears denominators in a basis to build a finite free complex over P that satisfies `TruncFibreExact` at 𝔮. `exists_basicOpen_truncFibreExact` spreads fibre exactness for a complex over a flat finite-type algebra with Cohen–Macaulay, equidimensional nonzero fibres of fixed dimension. `flat_baseChange_zero_of_truncFibreExact` applies the local criterion for flatness to the bottom cokernel at nearby primes.

## Scope

The openness result is the polynomial-ring case of the cited SGA result. The two polynomial-ring conclusions listed above allow R and M in separate universes. Their resolution argument uses a shared universe and passes to a quotient of a finite free module to obtain the general universe statement.

## References

Stacks Project, Tag 00MH, Tag 00MI, Tag 00RB and Tag 00RC. The lemma passing from stalks to localization at one element is tagged for flatness over the base in Tag 05IL and Tag 05IR. SGA 3 VIB 13.1(i).

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [05IL](https://stacks.math.columbia.edu/tag/05IL) | `flat_localizedModule_away_of_forall_flat_atPrime` | flatness over the base |
| [05IR](https://stacks.math.columbia.edu/tag/05IR) | `flat_localizedModule_away_of_forall_flat_atPrime` | flatness over the base |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 3 VIB 13.1 | `isOpen_setOf_flat_localizedModule_atPrime_mvPolynomial` | (i), special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Flat/OpenFlatLocusNoetherian.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 45 declarations of the source file 42 are kept. The 3 left out are not needed by the results for which the extract is made: `FreeComplexTruncation.truncD_of_gt`, `Stacks.Flatness.OpenFlatLocus.proj_comp_incl`, `Stacks.Flatness.OpenFlatLocus.range_comp_eq_range`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
