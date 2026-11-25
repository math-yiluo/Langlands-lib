# Complete discrete valuation rings and weak solutions

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.CompleteIntegralClosure`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file gives finiteness and completeness results for normalizations of complete discrete valuation rings (DVRs), and supplies the trivial weak solution and several induction steps for Epp’s theorem.

## Results

- `isDiscreteValuationRing_and_finite_integralClosure_of_isAdicComplete` shows that the integral closure of a maximal-ideal-adically complete DVR B in a finite extension M of its fraction field L is a finite B-module and a DVR. `isIntegralClosure_of_isAdicComplete` identifies any DVR C with fraction field M and a compatible local map from B with this normalization. `isAdicComplete_of_finite` gives maximal-ideal-adic completeness for a module-finite extension of DVRs over a complete base.
- `isWeakSolution_self` shows that the identity base-field extension gives a weak solution for a weakly unramified DVR extension. `exists_isWeakSolution_of_tower` passes a finite weak solution for A → C down to A → B in a compatible tower A → B → C.
- `induction_on_level` gives induction on rational levels 0 ≤ x < p when the step at x can use all nonnegative levels up to max(0, x − 1, 2x − p). `isWeaklyUnramified_of_extensionLevel_eq_zero` provides the base case for the specified mixed-characteristic cyclotomic polynomial and an integral-closure DVR extension.

The normalization result uses the finite fraction-field base-change theorem and the Nagata property of complete local rings. Completeness then passes to the finite module, using the equivalence of the two ideal-adic topologies.

A weak solution requires ramification index one at each maximal ideal of the normalized target. The tower lemma is the going-down direction of Tag 09ES. For B complete and M/L finite, finiteness over B and completeness of C follow from the results above.

The module docstring announces `p`-power residue lemmas, and the comment closing the file discusses lemmas on residue fields along finite extensions; none of them is in the file.

## References

Stacks Project Tag 09F8 and Tag 09ES. The finite normalization theorem is cited as a special case of SGA 6 X 7.16.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 6 X 7.16 | `isDiscreteValuationRing_and_finite_integralClosure_of_isAdicComplete` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppAlgClosedResidue/CompleteIntegralClosure.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 20 declarations of the source file 14 are kept. The 6 left out are not needed by the results for which the extract is made: `IsDiscreteValuationRing.exists_algebraMap_eq_of_forall_exists_pow`, `IsDiscreteValuationRing.forall_exists_pow_iff_of_finite`, `IsDiscreteValuationRing.forall_exists_pow_of_pow_eq`, `IsDiscreteValuationRing.isSeparable_of_forall_exists_pow`, `IsDiscreteValuationRing.minpoly_coeff_mem_of_forall_exists_pow`, `IsDiscreteValuationRing.residueField_forall_exists_pow_iff_of_finite`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
