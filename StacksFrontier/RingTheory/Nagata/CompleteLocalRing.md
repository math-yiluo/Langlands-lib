# Nagata property of complete local rings

Module `StacksFrontier.RingTheory.Nagata.CompleteLocalRing`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A Noetherian local ring complete for its maximal-ideal topology is Nagata. Each prime quotient is Japanese, meaning that its integral closure in every finite extension of its fraction field is module-finite.

`StacksIsNagataRing.of_isPrecomplete_maximalIdeal` gives this result, with the proof in `Stacks.Nagata.CompleteLocalRing.solution`. The private `isPrecomplete_of_surjective` also shows that adic precompleteness of a module passes through a surjective linear map. Its local-ring specialization supplies precompleteness of each prime quotient.

Adic completion preserves surjections, and the maximal ideal maps onto the maximal ideal of a local quotient. For each prime quotient, the Cohen structure theorem gives an injective finite map from a power series ring over a field or a Cohen ring. Fields are Japanese, and Tate's theorem gives the Cohen ring case using the residue field and the prime generating the maximal ideal. Iterating the one-variable power series theorem handles the source of the finite map, and Japanese ascent along injective quasi-finite maps handles the target.

The hypothesis is `IsPrecomplete` for the maximal ideal, which supplies surjectivity of the canonical completion map. For a Noetherian local ring, the Krull intersection theorem supplies the separatedness needed to assemble `IsAdicComplete`. The private quotient lemma applies to any surjection from a precomplete local ring to a local ring in the same universe. The conclusion is the class `StacksIsNagataRing`; the module docstrings write the class and the theorem without the prefix `Stacks`.

References include Tag 032W for the main theorem, Tag 032R for the Nagata definition, Tag 0325 for the quotient step, Tag 032D for the Cohen presentation, Tag 032I for ascent, Tag 032P for Tate's theorem, and Tag 032Q for power series. The table cites EGA 0 23.1.4 and EGA 0 23.1.5.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [032W](https://stacks.math.columbia.edu/tag/032W) | `StacksIsNagataRing.of_isPrecomplete_maximalIdeal` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 23.1.5 | `isJapaneseRing_of_isCohenRing` | special case |
| EGA | 0 23.1.5 | `isJapaneseRing_of_isField_or_isCohenRing` | special case |
| EGA | 0 23.1.4 | `isJapaneseRing_mvPowerSeries_fin` | more general |
| EGA | 0 23.1.5 | `isJapaneseRing_mvPowerSeries_fin` | special case |
| EGA | 0 23.1.5 | `isJapaneseRing_of_isPrecomplete_maximalIdeal` |  |
| EGA | 0 23.1.5 | `StacksIsNagataRing.of_isPrecomplete_maximalIdeal` | more general |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Nagata/CompleteLocalRing.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- Renamed, the source's name being declared elsewhere as well (`licenses/Stacks/STX-RENAMES.tsv.md`): `IsNagataRing.of_isPrecomplete_maximalIdeal` is `StacksIsNagataRing.of_isPrecomplete_maximalIdeal` here.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 6 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
