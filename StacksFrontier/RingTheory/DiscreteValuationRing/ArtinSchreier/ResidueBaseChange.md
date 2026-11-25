# Artin–Schreier layers: residues that are not p-th powers, and base change

Module `StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.ResidueBaseChange`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file continues the elimination of degree-p ramification for extensions of discrete valuation rings in characteristic p: Artin–Schreier parameters whose leading residue is not a p-th power, directly and after a totally ramified base change E/K, including over a prescribed orbit extension.

## Main results

- `isWeaklyUnramified_of_artinSchreier_residue_not_pow`: for B → C with fraction fields L ⊆ M, if M = L(z) with z^p − z = π^(−n) a, π a uniformizer of B, n > 0 divisible by p and the residue of a not a p-th power, then B → C is weakly unramified.
- `exists_baseChanged_laurent_reduction`: a Laurent reduction step for the prepared theorem.
- `exists_isWeakSolution_of_baseChanged_artinSchreier_residue`: for A → B → C and E/K finite separable with L ⊗_K E a field, given discrete valuation integral closures and a compatible injective map between them carrying the maximal ideal onto the maximal ideal, if the parameter ξ of M/L satisfies ξ − (t^p − t) = π^(−n) a, π a uniformizer of the closure of B, p ∣ n, n > 0 and the residue of a not a p-th power, then E/K is a weak solution for A → C.
- `exists_isWeakSolution_of_prepared_mixed_laurent_orbitExtension`: let A → B be weakly unramified and ξ a Laurent expansion, through a residue lift that is a ring homomorphism modulo m_B^n, with coefficients p^(depth i)-th powers of residue roots, depth i ≤ rank, and a distinguished index j whose root is not a p-th power and whose scaled pole (n − j) p^(rank − depth j) is positive, divisible by p and strictly largest. Then a finite Galois, totally ramified E/K of degree p^rank, with orbit data as produced by `exists_isGalois_totallyRamified_orbitExtension` at depth n + 1, is a weak solution for A → C.

## Points to watch

- `IsWeaklyUnramified`, `IsWeakSolution`, `IntegralClosureBaseChange` and `IsTotallyRamifiedWithRespectTo` are the library's own notions.
- Both weak-solution theorems take E, and the prepared one its orbit data and the facts about j, as inputs; E lies in the universe of K.
- The Laurent data and wild support of an Artin–Schreier presentation, which the module docstring announces, are not in the file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/ArtinSchreier/ResidueBaseChange.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 15 declarations of the source file 13 are kept. The 2 left out are not needed by the results for which the extract is made: `IsDiscreteValuationRing.exists_artinSchreier_laurent_data`, `IsDiscreteValuationRing.exists_wildSupport_of_laurent_data`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
