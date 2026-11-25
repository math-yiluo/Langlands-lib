# Finiteness of a module on principal opens

Module `StacksFrontier.RingTheory.LocalProperties.StandardCover`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file shows that finite generation of a module can be checked on a standard cover. The family f of elements of the commutative semiring R may have any index type, and `Ideal.span (Set.range f) = ⊤` says that the principal opens cover the spectrum.

- `Module.Finite.of_localizationSpan_range`: if each localization `LocalizedModule (Submonoid.powers (f i)) M` is finite over `Localization.Away (f i)`, then M is a finite R-module.

The proof reindexes Mathlib's `Module.Finite.of_localizationSpan` along the range of f. The result is part (2) of Tag 00EO; the setup docstring of the file speaks of all eight parts of that tag, of which only this one is in the file. A comment points to Mathlib's `Algebra.FiniteType.of_span_eq_top_target` and `Algebra.FinitePresentation.of_span_eq_top_target` for the target-cover statements of Tag 00EP. The references are SGA 4½ Arcata 1.4.2(ii) for module finiteness and SGA 4 IV 8.5.5 for the target-cover statements.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00EO](https://stacks.math.columbia.edu/tag/00EO) | `Module.Finite.of_localizationSpan_range` | (2) |
| [00EP](https://stacks.math.columbia.edu/tag/00EP) | `Algebra.FiniteType.of_span_eq_top_target` | (1) |
| [00EP](https://stacks.math.columbia.edu/tag/00EP) | `Algebra.FinitePresentation.of_span_eq_top_target` | (2) |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 4½ Arcata 1.4.2 | `Module.Finite.of_localizationSpan_range` | (ii) fin type, Zariski |
| SGA | 4 IV 8.5.5 | `Algebra.FiniteType.of_span_eq_top_target` | special case |
| SGA | 4 IV 8.5.5 | `Algebra.FinitePresentation.of_span_eq_top_target` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/LocalProperties/StandardCover.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 8 declarations of the source file 1 are kept. The 7 left out are not needed by the results for which the extract is made: `Algebra.FinitePresentation.of_localizationSpan_range`, `Algebra.FiniteType.of_localizationSpan_range`, `IsNoetherianRing.of_localizationSpan_range`, `Module.FinitePresentation.of_localizationSpan_range`, `Module.subsingleton_of_localizationSpan_range`, `bijective_of_localized_span_range`, `shortExact_of_localized_span_range`.
- 2 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 3 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
