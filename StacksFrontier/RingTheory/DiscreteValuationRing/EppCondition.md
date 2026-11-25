# Epp’s condition on the perfect core

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppCondition`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a local homomorphism A → B of local rings and exponential characteristic p of κ_B, `Stacks.EppTheorem.EppCondition` says that every element of the perfect core of κ_B is separable algebraic over κ_A. At p = 1, the definition requires κ_B/κ_A to be separable algebraic; Tag 09F9 imposes its perfect-core condition in positive residue characteristic.

- `EppCondition.of_residueField_surjective` transfers the condition from A → B to A′ → B′ in a compatible local ring square when κ_B → κ_B′ is surjective and the two target residue fields have the same exponential characteristic p.
- `IsDiscreteValuationRing.IsExtension.trans` gives transitivity of DVR extensions along a scalar tower A → B → C, by composition of injective local maps.

The module docstring also announces the condition spelled out with pⁿ-th roots and its ascent along separable closures of the residue fields; the file contains neither.

The file cites Epp’s *Elimination of wild ramification*, Tag 09F9 and Tag 09ET.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppCondition.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 7 declarations of the source file 3 are kept. The 4 left out are not needed by the results for which the extract is made: `Stacks.EppTheorem.EppCondition.of_isSepClosure`, `Stacks.EppTheorem.eppCondition_iff_forall_one_le`, `Stacks.EppTheorem.isAlgClosed_perfectCore_residueField`, `Stacks.EppTheorem.perfectCore_residueField_le_of_isSepClosure`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
