# Lowering the level of a mixed-characteristic degree-p extension

Module `StacksFrontier.RingTheory.DiscreteValuationRing.ExtensionLevel.LevelLowering`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file proves a base-change step for discrete valuation rings A → B → C with fraction fields K → L → M. It assumes mixed characteristic (0, p) with a perfect residue field of A, weakly unramified A → B, a uniformizer of A, and a cyclotomic quotient presentation of M/L of positive finite level ℓ.

- `exists_totallyRamified_isWeakSolution_or_extensionLevel_le_or_finiteSupport_of_uniformizer` has two alternatives. The first, `MixedLevelStepOutcome`, is a finite separable extension of K totally ramified with respect to A which is either a weak solution for A → C or gives a degree-p layer of level at most max(0, ℓ − 1, 2ℓ − p); in the level case both tensor products are fields, and the integral closure of B in the lower tensor field is a discrete valuation ring. The second is a finite coefficient set in the perfect core of κ_B with at least one element outside the image of κ_A.
- In the second alternative, `MixedLevelPreparation` retains the truncated polynomial and its lifting data. `MixedLevelStepReentry` then supplies the first alternative over a compatible weakly unramified base with perfect residue field, the same uniformizer image, and the indicated coefficients in its residue image.

The proof expands the parameter of least numerator n to precision m = min(n, e, pe − n), where e is the valuation of ζₚ − 1, and uses an Artin–Schreier shift when the coefficients descend to the base. A coefficient outside the perfect core leads to adjoining a p-power root of the uniformizer and isolating a leading residue outside the image of Frobenius, with a splitting argument available in either construction for a nonfield upper tensor product.

The theorem takes `hP`, giving `intProp`, `quotChar`, `shapeProp` and `funcEq` for the chosen P, alongside the finite-level presentation `hfinite`, and places the rings and fields in a common universe. The module docstring announces the two-alternative statement of Tag 09F5, without the finite-support branch; that statement is not in this file.

Reference is Stacks Project Tag 09F5.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/ExtensionLevel/LevelLowering.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 2 declarations of the source file 1 are kept. The 1 left out are not needed by the results for which the extract is made: `Stacks.DiscreteValuationRing.EppLevelInduction.exists_totallyRamified_isWeakSolution_or_extensionLevel_le`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
