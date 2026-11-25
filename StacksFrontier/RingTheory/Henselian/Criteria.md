# A complete local ring is henselian

Module `StacksFrontier.RingTheory.Henselian.Criteria`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file proves one criterion for henselianity.

- `henselianLocalRing_of_isAdicComplete_maximalIdeal` proves that a commutative local ring R that is adically complete for its maximal ideal m (`IsAdicComplete (IsLocalRing.maximalIdeal R) R`) is henselian, `HenselianLocalRing R`. The proof applies Mathlib’s `IsAdicComplete.henselianRing`, which gives the lifting property of R at m, and carries the hypothesis that f′(a₀) is a unit over to R/m along `Ideal.Quotient.mk`.

The module docstrings of the file still describe a strict henselianity criterion for normal local domains (Tag 0BSQ) and a criterion for Krull dimension zero, with their auxiliary lemmas; neither result is in the file.

The result is Tag 04GM and cites EGA IV 18.5.14, EGA IV 18.5.16 and SGA 3 X 4.0.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [04GM](https://stacks.math.columbia.edu/tag/04GM) | `henselianLocalRing_of_isAdicComplete_maximalIdeal` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 18.5.14 | `henselianLocalRing_of_isAdicComplete_maximalIdeal` | local case |
| EGA | IV 18.5.16 | `henselianLocalRing_of_isAdicComplete_maximalIdeal` | special case |
| SGA | 3 X 4.0 | `henselianLocalRing_of_isAdicComplete_maximalIdeal` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Henselian/Criteria.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 15 declarations of the source file 1 are kept. The 14 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 3 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
