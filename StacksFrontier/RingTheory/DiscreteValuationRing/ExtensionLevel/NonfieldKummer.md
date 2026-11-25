# Weak solutions from a split Kummer base change

Module `StacksFrontier.RingTheory.DiscreteValuationRing.ExtensionLevel.NonfieldKummer`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let A ⊆ A′ ⊆ B be a tower of extensions of discrete valuation rings, with fraction fields K ⊆ M ⊆ L. The file constructs a weak solution to the base-change problem when a prime-degree Kummer extension splits after an auxiliary base change.

`exists_weakSolution_of_nondivisible_kummer_nonfield` assumes that A ⊆ A′ is weakly unramified and L/M is Galois of prime degree p. A generator of L/M is given whose pth power is uπᵐ, with u a unit of A′, π a uniformizer of A′, and m an integer prime to p. The auxiliary extension E/K is separable and totally ramified of degree p, with integral closure of A a DVR. The theorem assumes that M ⊗ₖ E is a field and L ⊗ₖ E is not a field. It produces an `IntegralClosureBaseChange` package over E satisfying `IsWeakSolution`. Every maximal ideal of the upper integral closure has ramification index one over the lower integral closure.

The proof uses the prime-degree Kummer presentation to identify M ⊗ₖ E with L over M. Evaluation at the Galois automorphisms then splits L ⊗ₖ E as a product of copies of L, and the integral closure of B in that product is a product of copies of B. Bézout's identity replaces the Kummer generator by a pth root of a unit times the uniformizer. The valuation bound and weakly unramified lower step give ramification index p for B over A. The lower integral closure also has index p by total ramification, so the tower formula gives index one at each localized factor.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/ExtensionLevel/NonfieldKummer.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 31 declarations of the source file 24 are kept. The 7 left out are not needed by the results for which the extract is made: `Stacks.GaloisTensorSplitting.baseChangeSplittingEquiv_left`, `Stacks.GaloisTensorSplitting.baseChangeSplittingEquiv_right`, `Stacks.GaloisTensorSplitting.baseChangeSplittingEquiv_tmul`, `Stacks.GaloisTensorSplitting.closureEquivOfSplitting_apply`, `Stacks.GaloisTensorSplitting.evaluationHom_tmul`, `Stacks.GaloisTensorSplitting.productClosureEquiv_apply`, `Stacks.GaloisTensorSplitting.splittingEquiv_tmul`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
