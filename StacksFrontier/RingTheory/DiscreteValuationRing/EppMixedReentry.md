# Transport of Epp’s residue condition

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppMixedReentry`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file transports the residue condition used in the mixed-characteristic degree-p descent. The condition identifies the image of the base residue field with the elements upstairs that admit pⁿ-th roots for all n ≥ 1.

`forall_exists_pow_iff_of_algEquiv_square` transfers the condition `h` on one horizontal map to the other in a commuting square of commutative rings with vertical algebra equivalences. Commutativity of the square is the hypothesis `hsq`.

`surjective_residueField_map_of_totallyRamified` gives a surjective residue map for a finite separable fraction-field extension totally ramified with respect to the DVR, when the integral closure is a DVR with local structure map. `surjective_algebraMap_residueField_of_surjective_map` turns a surjective residue map κ_A → κ_B of a local homomorphism A → B into surjectivity of A → κ_B, and `surjective_algebraMap_residueField_of_totallyRamified` combines the two.

The vertical equivalences carry power roots in both directions, and commutativity identifies the ranges. Total ramification makes the residue extension of degree one, hence bijective.

The square lemma uses compatible equivalences over the respective base rings. In the DVR application the two residue equivalences come from the base-change construction. The module docstring also announces bounds on the extension level, a criterion for weak unramifiedness and the commutativity of the square under surjectivity, which the file does not contain.

References include hypothesis (5) of Tag 09F5 and the totally ramified base change of Tag 09ER.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppMixedReentry.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 11 declarations of the source file 4 are kept. The 7 left out are not needed by the results for which the extract is made: `Stacks.DegreePExtensionLevel.extensionLevel_eq_zero_iff`, `Stacks.DegreePExtensionLevel.extensionLevel_lt_of_isDegreePExtensionOfFiniteLevel`, `Stacks.DegreePExtensionLevel.extensionLevel_nonneg`, `Stacks.DiscreteValuationRing.EppLevelInduction.algEquiv_square_comm_of_surjective`, `Stacks.DiscreteValuationRing.EppLevelInduction.forall_exists_pow_iff_of_surjective`, `Stacks.DiscreteValuationRing.EppLevelInduction.isWeaklyUnramified_of_map_maximalIdeal_eq`, `Stacks.DiscreteValuationRing.EppLevelInduction.isWeaklyUnramified_of_map_maximalIdeal_eq_of_ringHom_eq`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
