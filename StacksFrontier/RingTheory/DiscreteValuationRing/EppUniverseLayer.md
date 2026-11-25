# Epp’s theorem in independent universes

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppUniverseLayer`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file derives Epp’s theorem for an extension of discrete valuation rings A → B whose rings and fraction fields K and L may lie in four different universes. The resulting finite solution field lies in the universe of K.

- `exists_field_descent_ulift` takes a finite extension E of `ULift K` and produces a finite extension K₁/K in the universe of K. It gives a ring isomorphism from `ULift K₁` to E that respects the two maps from K.
- Given an algebra equivalence `eUK₁` from `ULift K₁` to a field K₁′ over `ULift K`, `uliftTensorRingEquiv` identifies `ULift L ⊗[ULift K] K₁′` with L ⊗[K] K₁. `uliftCompositumRingEquiv` induces the same identification on the reductions. The accompanying lemmas compute both maps on the tensor factors.
- `eppTheorem_of_monomorphic` derives the four-universe proposition `Stacks.EliminateRamification.EppTheorem` from `h`, the same proposition at the common universe given by the maximum of the four.

The proof lifts the rings, fields, and residue-field condition to that common universe and applies `h`. It replaces the resulting package by the canonical one, descends the finite field, and transports the weak solution along commuting isomorphisms of integral closures.

Field descent is expressed by a ring isomorphism with a compatibility equation, so the statement uses the given `Algebra (ULift K) E` instance throughout.

The comments cite Tag 09EM, Tag 09F9, and Tag 09II.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppUniverseLayer.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
