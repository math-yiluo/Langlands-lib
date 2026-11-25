# Inertia fixed fields and cyclotomic rings

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.IntermediateFieldInduction`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file proves two facts on the inertia group of a local ring and its fixed field, and one on adjoining roots of unity over a field of characteristic zero.

## Results

- `formallyUnramified_integralClosure_fixedField_inertia` applies to a finite Galois extension L of the fraction field K of a DVR A. If the normalization of A in L is local, and so is its normalization in the fixed field E of the inertia group of the maximal ideal, then the latter is formally unramified over A.
- `normal_inertia_maximalIdeal` gives normality of the inertia subgroup of the maximal ideal for a group acting on a local ring by ring automorphisms.
- `exists_finite_extension_nonempty_cyclotomicRingHom` starts with a commutative ring A mapped to a characteristic-zero field K and a positive integer n. It gives a finite extension of K, in the universe of K, whose integral closure of A receives a map from the n-th cyclotomic ring.

The first result identifies the normalization in E with the inertia invariants of the normalization in L, whose localization at its maximal ideal is étale over A; a local ring equals that localization. The third takes the n-th cyclotomic field over K, embeds the cyclotomic field over ℚ in it, and uses integrality of the cyclotomic ring over ℤ.

## Points to watch

- The module docstring announces the prime-degree step, the induction over intermediate fields and Epp's theorem in the complete case (Tag 09F8); none of them is in the file.

## References

The formal-unramifiedness result for the inertia fixed field is cited as part of SGA 7 I 0.3.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 7 I 0.3 | `formallyUnramified_integralClosure_fixedField_inertia` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppAlgClosedResidue/IntermediateFieldInduction.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 12 declarations of the source file 3 are kept. The 9 left out are not needed by the results for which the extract is made: `IsDiscreteValuationRing.exists_finite_extension_isWeakSolution`, `IsDiscreteValuationRing.exists_finite_extension_isWeakSolution_of_intermediateField_induction`, `IsDiscreteValuationRing.exists_finite_extension_isWeakSolution_of_normal_factor_induction`, `IsDiscreteValuationRing.exists_finite_extension_isWeakSolution_of_normal_same_universe`, `IsDiscreteValuationRing.exists_finite_extension_isWeakSolution_of_prime_degree`, `IsDiscreteValuationRing.exists_finite_extension_isWeakSolution_of_same_universe`, `IsDiscreteValuationRing.isIntegralClosure_and_finite_and_isAdicComplete`, `IsDiscreteValuationRing.isScalarTower_of_isScalarTower_top`, `IsDiscreteValuationRing.normalTowerSolvable`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
