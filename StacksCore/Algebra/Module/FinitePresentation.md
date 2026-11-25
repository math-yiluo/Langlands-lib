# Finite presentation in short exact sequences

Module `StacksCore.Algebra.Module.FinitePresentation`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let `R` be a ring and `0 → M1 → M2 → M3 → 0` a sequence of `R`-modules, given by linear maps `f`, `g` that are exact at `M2`. The file proves one of the two-out-of-three statements for finite presentation.

- `Module.FinitePresentation.of_exact_fst`: if `f` is injective, `g` surjective, and `M1`, `M3` are finitely presented, then `M2` is finitely presented.

The proof identifies `M1` with `ker g` (private `kerEquivOfExact`), so that `ker g` is finitely presented, and applies Mathlib's `Module.finitePresentation_of_ker`.

Only part 2 of Tag 0519 is here.

References: Tag 0519. The table of tags below also attributes Mathlib's `Module.FinitePresentation` to Tag 0518 (part 2), and Mathlib's lemmas on localizing linear maps out of finitely presented modules (`Module.FinitePresentation.isLocalizedModule_map` and related) to Tag 0583.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0519](https://stacks.math.columbia.edu/tag/0519) | `Module.FinitePresentation.of_exact_fst` | 2 |
| [0518](https://stacks.math.columbia.edu/tag/0518) | `Module.FinitePresentation` | part 2 |
| [0583](https://stacks.math.columbia.edu/tag/0583) | `instIsLocalizedModuleLinearMapIdLocalizationLocalizedModuleMapOfFinitePresentation` | part 1 |
| [0583](https://stacks.math.columbia.edu/tag/0583) | `Module.FinitePresentation.isLocalizedModule_mapExtendScalars` | part 1 |
| [0583](https://stacks.math.columbia.edu/tag/0583) | `Module.FinitePresentation.isLocalizedModule_map` | part 2 |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksCore/Algebra/Module/FinitePresentation.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 4 declarations of the source file 2 are kept. The 2 left out are not needed by the results for which the extract is made: `Module.Finite.of_exact_left`, `Module.FinitePresentation.of_exact_third`.
- 2 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
