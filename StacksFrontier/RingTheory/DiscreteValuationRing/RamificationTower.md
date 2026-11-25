# Ramification indices in towers

Module `StacksFrontier.RingTheory.DiscreteValuationRing.RamificationTower`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For compatible injective algebra maps A → B → C of discrete valuation rings, the file proves that ramification indices multiply. Here e is the library's `ramificationIdx` and v the additive valuation `addVal`.

`addVal_algebraMap_eq_mul` scales a finite valuation by the ramification index: v_A(a) = n gives v_B(a) = e(B/A) · n. Applied to a uniformizer, this gives `ramificationIdx_trans`, namely e(C/A) = e(B/A) · e(C/B). From e(C/A) = 1, `isWeaklyUnramified_of_isWeaklyUnramified` deduces that both factors are one.

The module docstring also announces results on squares of prime ideals and on weak solutions after base change, which the file does not contain; its `Ideal` namespace is empty, and its `IsDiscreteValuationRing.IntegralClosureBaseChange` section only switches on local instances.

The file cites Tag 09E6 and Tag 09ES. The valuation scaling lemma is a partial result for SGA 7 IX 10.3.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 7 IX 10.3 | `addVal_algebraMap_eq_mul` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/RamificationTower.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 12 declarations of the source file 3 are kept. The 9 left out are not needed by the results for which the extract is made: `Ideal.ramificationIdx_eq_one_iff_ramificationIdx_vertical_eq`, `Ideal.ramificationIdx_eq_one_iff_ramificationIdx_vertical_le`, `Ideal.ramificationIdx_eq_one_of_finiteEtale_square`, `Ideal.ramificationIdx_vertical_dvd_of_ramificationIdx_eq_one`, `IsDiscreteValuationRing.IntegralClosureBaseChange.IsWeakSolution.of_finiteEtale_square`, `IsDiscreteValuationRing.IntegralClosureBaseChange.IsWeakSolution.of_ramificationIdx_vertical_eq`, `IsDiscreteValuationRing.IntegralClosureBaseChange.IsWeakSolution.of_ramificationIdx_vertical_le`, `Stacks.DiscreteValuationRing.Ramification.ramificationIdx_eq_of_isWeaklyUnramified`, `Stacks.DiscreteValuationRing.Ramification.ramificationIdx_eq_of_mul_eq_of_le`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
