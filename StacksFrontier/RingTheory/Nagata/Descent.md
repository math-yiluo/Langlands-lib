# Descent of the Japanese and Nagata conditions

Module `StacksFrontier.RingTheory.Nagata.Descent`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file proves descent of the universally Japanese and Nagata conditions from a principal open cover.

`isUniversallyJapaneseRing_and_isNagataRing_of_localizationSpan`, proved by `Stacks.Nagata.PrincipalOpenDescent.solution`, takes a set `t` generating the unit ideal of a commutative ring `R` and an away localization for each element of `t`. If every localization is universally Japanese, so is `R`. If every localization is Nagata, so is `R`. The two implications have independent hypotheses.

For the cover theorem, a finite-type domain over `R` is tested on the nonzero images of `t`, where its localizations are finite type over the base localizations. The Nagata argument uses the same Japanese descent on prime quotients, since localization commutes with taking those quotients. Noetherianity descends by testing finite generation of ideals on the cover.

The cover permits arbitrary spanning sets and abstract models of the localizations in the universe of `R`. The Nagata condition is the class `StacksIsNagataRing`. The last module docstring still announces Nagata descent along an extension of discrete valuation rings with separable fraction-field extension (Tag 0GLS); that theorem is not in the file, and the namespace `StacksIsNagataRing` at the end of the file is empty.

References are Tag 032V for principal open descent, Tag 032H for Japanese descent, and Tag 00EO (6) for Noetherian descent.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [032V](https://stacks.math.columbia.edu/tag/032V) | `isUniversallyJapaneseRing_and_isNagataRing_of_localizationSpan` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Nagata/Descent.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 12 declarations of the source file 8 are kept. The 4 left out are not needed by the results for which the extract is made: `IsNagataRing.of_isSeparable_fractionRing`, `finite_integralClosure_of_separable_fraction_extension`, `isJapaneseRing_of_isField`, `isNagataRing_of_isJapaneseRing`.
- 1 command that is not a declaration is left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
