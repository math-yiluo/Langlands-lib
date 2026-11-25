# Weak solutions for the canonical base-change package

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppUniverseAssembly`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For an extension A → B of discrete valuation rings with fraction fields K and L and a finite extension K₁/K, the file transfers the weak-solution property from any presentation to the canonical one. Its carriers are the reduction of L ⊗[K] K₁ and the integral closures of A in K₁ and of B in that reduction.

`algebraMap_eL₁_base` shows that the package’s compositum equivalence preserves the structure map from B. With `hD` asserting that a given package D is a weak solution, `isWeakSolution_canonicalBaseChange_of_isWeakSolution` proves that `canonicalBaseChange` over the same K₁ is a weak solution.

The proof uses uniqueness of the two integral closures to build a commuting square of ring equivalences, which preserves the ramification indices. The transfer uses the supplied solution and permits independent universes for the original package carriers.

The comments cite Tag 09EM and Tag 09F9.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppUniverseAssembly.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
