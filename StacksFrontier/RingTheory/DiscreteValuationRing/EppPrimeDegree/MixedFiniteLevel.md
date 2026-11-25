# Finite-level descent in mixed characteristic

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppPrimeDegree.MixedFiniteLevel`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file turns mixed-characteristic finite-level presentations of degree-p extensions into weak solutions. The descent tracks both the rational extension level and the least admissible numerator of a presentation.

`exists_finite_extension_isWeakSolution_of_mixedFiniteLevel` takes a DVR tower A ⊆ B ⊆ C with fraction fields K ⊆ L ⊆ M, where K has characteristic zero, A and B are complete, and the residue field of A is perfect of characteristic p for prime p. It assumes A → B is weakly unramified, M/L is finite, and the residue fields satisfy `EppCondition A B p`. The input includes a cyclotomic map f into B, a polynomial P satisfying `intProp`, `quotChar`, `shapeProp` and `funcEq`, and `hfinite : IsDegreePExtensionOfFiniteLevel B L M p f P`. It yields a finite extension of K with a weak `IntegralClosureBaseChange` solution for A → C.

The private predicates `MixedFiniteLevelUpToSolvable` and `MixedFiniteNumeratorUpToSolvable` encode the induction at a level bound and at a fixed least numerator, respectively. The cyclotomic uniformizer gives an initial level in [0, p). At zero the top layer is weakly unramified. A successful positive-level step either supplies a solution or gives a totally ramified base change with level bounded by max(0, ℓ − 1, 2ℓ − p), where the outer induction applies.

For the finite-support alternative, one weakly unramified extension absorbs the support in every reduced tensor factor. Degree-one factors are already weakly unramified. In a degree-p factor the mapped preparation either gives a successful level step or strictly lowers the least numerator within the old level bound. Strong induction on that numerator solves the latter factors, and the factor solutions are combined and descended.

The theorem works in one universe and requires the finite-level cyclotomic presentation as input.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppPrimeDegree/MixedFiniteLevel.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
