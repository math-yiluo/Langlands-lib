# Completeness of modules for adic filtrations

Module `StacksFrontier.RingTheory.AdicCompletion.Basic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a module M over a commutative ring R, the I-adic completion is the inverse limit of M/IⁿM. The file gives two criteria for I-adic completeness of a module. It uses Mathlib's `IsAdicComplete`, which combines separatedness (`IsHausdorff`) and convergence of Cauchy sequences (`IsPrecomplete`).

## Results

- `completeness_preserved` gives equivalence of I-adic and J-adic completeness when Iᶜ ⊆ J and Jᵈ ⊆ I for positive integers c and d. The two halves transfer separately: `Stacks.AdicCompletionComparison.haus_imp` carries separatedness from I to J using only Jᵈ ⊆ I, and `Stacks.AdicCompletionComparison.prec_imp` carries precompleteness using both inclusions, through the inclusion I^(cn)M ⊆ JⁿM of `Stacks.AdicCompletionComparison.incl`.
- `isAdicComplete_of_iInf_smul_eq_bot` gives I-adic completeness for a finite R-module M over an I-adically complete ring R under the separatedness hypothesis ⋂ₙ IⁿM = 0.

The precompleteness transfer takes a limit of a subsequence of the given Cauchy sequence; the finite-module criterion uses surjectivity of the comparison from the tensor product with the completed ring.

The module docstring and the section docstrings also announce a surjectivity criterion for a finitely generated ideal, the passage to a smaller finitely generated ideal, an isomorphism of the completions for cofinal ideals and a completeness criterion for quotients; none of these is in the file.

## References

The cofinality result is Tag 0319 ("in particular") and the finite-module result is Tag 031B. A closing comment relates Tag 0317 to Mathlib's `IsAdicComplete` and `AdicCompletion.of_bijective_iff`.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0319](https://stacks.math.columbia.edu/tag/0319) | `completeness_preserved` | in particular |
| [031B](https://stacks.math.columbia.edu/tag/031B) | `isAdicComplete_of_iInf_smul_eq_bot` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/AdicCompletion/Basic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 18 declarations of the source file 5 are kept. The 13 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- 1 command that is not a declaration is left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
