# Descent and composition of Epp solutions in towers

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppSolution`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a compatible tower A → B → C of extensions of discrete valuation rings with fraction fields K → L → M, the file compares base changes along a finite extension K₁/K. It treats weak solutions, which ask for ramification index one at every maximal ideal of the upper integral closure, and solutions, which ask for adic formal smoothness on the corresponding localizations.

- `baseClosureEquiv` identifies the two presentations of the integral closure of A in K₁. `reducedCompositumMap` is the map from the reduction of L ⊗[K] K₁ to that of M ⊗[K] K₁ induced by L → M, expressed on the given base-change packages. `targetClosureMap` restricts this to the upper integral closures, extending B → C. The comparison lemmas verify the commuting squares with the structure maps.
- `ramificationIdx_eq_one_iff_isWeaklyUnramified` identifies the index-one condition at a prime with weak unramifiedness of the localized extension when both localizations are discrete valuation rings and the induced map between them is an extension of discrete valuation rings (`IsExtension`).
- `weakSolutions_and_solutions_go_down_and_compose` shows that a weak solution or a solution for A → C over K₁ descends to the corresponding property for A → B. For composition, the lower reduced tensor product is given as a nonempty finite product of fields Eᵢ finite over L. If the lower package over K₁ and all the upper packages for B → C over their respective Eᵢ are weak solutions, then so is the full package over K₁. The analogous implication holds for solutions.

For descent, faithful flatness over the middle discrete valuation ring and an integral tensor comparison with nilpotent kernel elements lift maximal ideals to the top closure. For composition, reduced tensor products and integral closures split compatibly over the given factors, so each top maximal ideal is treated in one factor. The localized arguments use descent and transitivity of weak unramifiedness and adic formal smoothness.

The composition hypothesis ranges over all factors and uses the explicit packages `DBC` over those factors. The ring, field, and presentation universes are independent. Each solution uses the maximum of the two integral-closure universes for its formal smoothness condition.

The tower theorem is Tag 09ES. The comments cite Tag 09E7 for the residue-field characterization of adic formal smoothness.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [09ES](https://stacks.math.columbia.edu/tag/09ES) | `weakSolutions_and_solutions_go_down_and_compose` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppSolution.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 41 declarations of the source file 40 are kept. The 1 left out are not needed by the results for which the extract is made: `IsDiscreteValuationRing.ker_tensorMap_le_nilradical`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
