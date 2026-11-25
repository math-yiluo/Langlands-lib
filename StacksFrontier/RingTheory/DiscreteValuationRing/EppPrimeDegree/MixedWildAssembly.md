# Mixed-characteristic prime-degree solutions and tower assembly

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppPrimeDegree.MixedWildAssembly`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file proves the wild prime-degree step in mixed characteristic and combines it with the equal-characteristic, tame and purely inseparable steps into the finite normal-family recursion for complete DVR towers over a perfect residue field.

`MixedWildPrimeDegreeSolvable p` states that a DVR tower A ⊆ B ⊆ C, with fraction fields K ⊆ L ⊆ M, has a finite weak solution for A → C under the mixed-characteristic wild hypotheses. It requires characteristic zero for K, prime residue characteristic p, perfect residue field for A, completeness of A and B, a weakly unramified lower layer satisfying `EppCondition`, and a finite Galois top layer of degree p. `mixedWildPrimeDegreeSolvable` proves this proposition.

`wildPrimeDegreeSolvable_of_mixedWildPrimeDegreeSolvable` combines a supplied mixed-characteristic solver `hmixed` with the Artin–Schreier solver. `familyTowerSolvable_all_of_mixedWildPrimeDegreeSolvable` then obtains the finite normal-family recursion `FamilyTowerSolvable p n` at every degree bound n, and `familyTowerSolvable_all_proved` discharges `hmixed` using the result of this file.

The mixed proof first adjoins the cyclotomic parameter to K and matches upper and lower reduced tensor factors. Degree-p factors use the totally ramified reduction to a direct solution or to a finite-level presentation. Smaller degrees are prime to p, so the already weakly unramified lower layer and perfect base residue field allow the tame solver. Combining the solutions for all factors yields the original tower solution.

The module docstring also announces Epp's theorem for perfect fields; the file stops at the family recursion and does not state it.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppPrimeDegree/MixedWildAssembly.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 7 declarations of the source file 6 are kept. The 1 left out are not needed by the results for which the extract is made: `Stacks.EppTheorem.exists_finite_extension_isWeakSolution_of_perfectField_proved`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
