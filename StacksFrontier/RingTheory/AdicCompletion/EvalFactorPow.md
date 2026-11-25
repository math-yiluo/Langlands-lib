# Reduction maps for adic quotients

Module `StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file relates evaluation on the adic completion of a commutative ring to transitions between quotients by powers of an ideal.

For an ideal I of A and a commutative A-algebra B, `Ideal.quotientMapPowAlgEquiv` identifies the quotient of B by the extension of Iⁿ with its quotient by (IB)ⁿ, as A-algebras. Both directions preserve residue classes. For a ring map f from A to B, `Ideal.Quotient.factorPow_comp_quotientMap` shows that reductions from level n to m commute with the maps induced by f, given m ≤ n, a source ideal J and a target ideal I for which f sends Jⁿ into Iⁿ and Jᵐ into Iᵐ.

`AdicCompletion.stacks_factorPow_evalₐ` says that reducing the level-n evaluation to level m gives the level-m evaluation. The lemmas `AdicCompletion.evalₐ_eq_mk` and `AdicCompletion.val_eq_mk` pass between the ring and module quotient descriptions of a residue.

The square is checked on representatives, and evaluation compatibility follows from the defining congruences of a completion element.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/AdicCompletion/EvalFactorPow.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- Renamed, the source's name being declared elsewhere as well (`licenses/Stacks/STX-RENAMES.tsv.md`): `AdicCompletion.factorPow_evalₐ` is `AdicCompletion.stacks_factorPow_evalₐ` here.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
