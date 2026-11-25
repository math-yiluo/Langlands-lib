# Field factors of a base change and composition of weak solutions

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedFactorSync.WildLayerDescent`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file supplies the field factors of a finite base change with all carriers in one universe, and a composition theorem for weak solutions along a tower of discrete valuation rings.

- `exists_finiteFieldFactors_of_package` takes a base-change package D of A → B along a finite extension K₁/K, all carriers in one universe, and gives a nonempty decomposition of D.L₁ into fields finite over L, compatible with the maps from K₁. `exists_finiteSeparableFieldFactors_of_package` gives factors separable over L when K₁/K is separable.
- `isWeakSolution_of_prime_layer_of_forall_factor` composes a weak solution of the lower layer A → B over K₁ with a weak solution of the upper layer B → C over each respective lower factor, yielding a weak solution of the full tower A → C over K₁.

The first theorem is `IsDiscreteValuationRing.finiteFieldFactors_compatible` with its universes made equal, so that the factors live in the universe of the input. The second obtains separable factors from the description of the integral closures after a finite fraction-field extension. The composition is the weak-solution implication of Tag 09ES, stated as a direct implication; it applies at arbitrary finite base-change degree, leaves all universes free, and uses the factors only in its hypotheses.

The module docstring also announces a shared wild extension and a descent on intermediate fields, which the file does not contain; the two sections meant for them are empty.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppSharedFactorSync/WildLayerDescent.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 8 declarations of the source file 3 are kept. The 5 left out are not needed by the results for which the extract is made: `Stacks.EppTheorem.exists_sharedExtension_factorSolutions_of_prepared_wild_or_isWeaklyUnramified`, `Stacks.EppTheorem.forall_solves_intermediateField_of_prescribed`, `Stacks.EppTheorem.solves_intermediateField_of_prescribed`, `Stacks.EppTheorem.solves_intermediateField_of_prescribed_isPurelyInseparable`, `Stacks.EppTheorem.solves_of_finrank_descent`.
- 1 command that is not a declaration is left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
