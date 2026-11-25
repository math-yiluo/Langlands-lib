# The Japanese property across universes

Module `StacksFrontier.RingTheory.Nagata.Shrink`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file transports module-finiteness of integral closures to field extensions in arbitrary Lean universes.

`module_finite_integralClosure_of_isJapaneseRing` proves that the integral closure of a Japanese domain A in any finite extension L of a fraction field F of A is finite over A. The algebra structures on A → F → L must form a scalar tower. The class `IsJapaneseRing` tests extensions of the canonical `FractionRing A` in A's own universe.

The proof transports the extension along the fraction-field isomorphism, shrinks L into A's universe, then carries finiteness back by an A-algebra equivalence. `small_of_finite_field` supplies smallness for finite-dimensional vector spaces, and `shrink_isScalarTower` transports the tower to the shrunk copy. `Module.Finite.integralClosure_of_ringEquiv` transports finiteness between isomorphic base rings whose maps into the fixed ambient ring agree through the isomorphism.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Nagata/Shrink.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
