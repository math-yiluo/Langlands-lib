# Persistence of solutions in finite field towers

Module `StacksFrontier.RingTheory.DiscreteValuationRing.SolutionTower`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let A → B be an injective local map of discrete valuation rings with compatible fraction fields K → L. The file shows that a solution for A → B remains a solution after enlarging its finite base field extension.

`exists_isSolution_of_tower` takes a compatible tower K → K₁ → K₂ with both steps finite. The hypothesis `hsolution` supplies an integral-closure base-change package at K₁ whose local maps are formally smooth for the target maximal-ideal adic topology. The conclusion gives such a package at K₂ over the original A → B.

`isLocalization_reduction` identifies the reduction of a localization with the localization of the reduction at the image of the original multiplicative set, with compatible algebra structures. `integralClosureMapOfScalarTower` takes integral elements to integral elements along a compatible algebra map even when the base ring also changes.

The proof compares the reduction of L ⊗[K] K₂ with the reduction of F ⊗[K₁] K₂, where F is the reduction of L ⊗[K] K₁. After tensoring, the quotient map for the intermediate reduction is still surjective with nil kernel. The new integral closures are taken over the first pair of integral closures and identified as closures over A and B by transitivity of integrality. At each maximal ideal the proof localizes and invokes `formallySmooth_localizations_after_finite_fraction_field_extension` on the resulting discrete valuation rings.

The theorem applies to inseparable as well as separable finite towers. The tower comparison uses the final reduction on both sides. The input carriers have independent universes, while the first and second solution predicates test formal smoothness in the maximum of the two localization-carrier universes for the respective base change.

The persistence theorem is Tag 0GLR. Tag 09E7 is cited for the universe choice in the formal-smoothness criterion.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0GLR](https://stacks.math.columbia.edu/tag/0GLR) | `exists_isSolution_of_tower` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/SolutionTower.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 21 declarations of the source file 20 are kept. The 1 left out are not needed by the results for which the extract is made: `IsDiscreteValuationRing.integralClosureMapOfScalarTower_apply`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
