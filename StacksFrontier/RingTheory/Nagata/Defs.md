# Finite integral closure and Nagata rings

Module `StacksFrontier.RingTheory.Nagata.Defs`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file defines finiteness properties for normalization and integral closure in finite field extensions, and uses them to define the universally Japanese and Nagata conditions on commutative rings.

- `StacksIsN1 R` abbreviates module finiteness of the integral closure of `R` in `FractionRing R`. For a domain this says its normalization is finite over it.
- `IsJapaneseRing R` is a class for domains. The class field `IsJapaneseRing.finite`, registered as an instance, gives finiteness of the integral closure of `R` in each finite-dimensional extension of `FractionRing R` with the compatible scalar tower.
- `IsUniversallyJapaneseRing R` requires each finite-type domain algebra over `R` to be Japanese.
- `StacksIsNagataRing R` requires Noetherianity and the Japanese condition for every prime quotient. An instance projects Noetherianity from this class.

The N-2 abbreviations `IsN2Aux`, `IsN2_032k`, `IsN2_032s`, and `IsN2_032u` use the canonical fraction ring.

These are the Stacks library's predicates. `StacksIsN1` also applies to commutative rings with zero divisors, using the total ring of fractions. The class definitions and the N-2 abbreviations quantify over finite extension fields or finite-type domain algebras in the universe of the base. The module docstring writes the N-1 predicate and the Nagata class without the prefix `Stacks`, and still lists N-1 and N-2 variants over a specified fraction field and a second form of the universally Japanese condition, which are not in the file.

References are Tag 032F for N-1 and N-2, Tag 032R for the universally Japanese and Nagata conditions, Tag 0351, and Grothendieck and Dieudonné's *Éléments de géométrie algébrique*, EGA 0 23.1.1 and EGA IV 7.7.1.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [032F](https://stacks.math.columbia.edu/tag/032F) | `StacksIsN1` | (1) |
| [032F](https://stacks.math.columbia.edu/tag/032F) | `IsJapaneseRing` | (2) |
| [032R](https://stacks.math.columbia.edu/tag/032R) | `IsUniversallyJapaneseRing` | (1) |
| [032R](https://stacks.math.columbia.edu/tag/032R) | `StacksIsNagataRing` | (2) |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 23.1.1 | `IsJapaneseRing` | def. of Japanese |
| EGA | 0 23.1.1 | `IsUniversallyJapaneseRing` |  |
| EGA | IV 7.7.1 | `IsUniversallyJapaneseRing` |  |
| EGA | 0 23.1.1 | `IsN2_032u` |  |
| EGA | 0 23.1.1 | `IsN2_032s` |  |
| EGA | 0 23.1.1 | `IsN2_032k` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Nagata/Defs.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 19 declarations of the source file 16 are kept. The 3 left out are not needed by the results for which the extract is made: `IsN1_032m`, `IsN2_032m`, `IsUniversallyJapanese`.
- Renamed, the source's name being declared elsewhere as well (`licenses/Stacks/STX-RENAMES.tsv.md`): `IsN1` is `StacksIsN1` here; `IsNagataRing` is `StacksIsNagataRing` here; `IsNagataRing.isJapaneseRing_quotient` is `StacksIsNagataRing.isJapaneseRing_quotient` here; `IsNagataRing.isNoetherianRing` is `StacksIsNagataRing.isNoetherianRing` here; `IsNagataRing.mk` is `StacksIsNagataRing.mk` here.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 6 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
