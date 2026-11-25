# Reduced base change along separable algebraic extensions

Module `StacksFrontier.RingTheory.GeometricallyReduced.SeparableBaseChange`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A reduced algebra over a field stays reduced after separable algebraic base change.

In `Stacks.GeometricallyReduced.SeparableBaseChange`, `isReduced_tensorProduct_of_isSeparable` proves that the tensor product of K and T over F is reduced for a separable algebraic extension K/F and a reduced commutative F-algebra T. `isReduced_tensorProduct_of_finiteDimensional` proves the finite extension case. Supporting lemmas descend reducedness along an injection of either tensor factor when the other is flat, and test field base changes on finitely generated subextensions. The theorem `isReduced_congr`, placed in the root namespace, proves that reducedness of commutative rings is invariant under a ring isomorphism.

The proof passes to finite subextensions of K and finitely generated subalgebras of T. In the Noetherian case, the algebra embeds into the product of its localizations at minimal primes, and formal unramifiedness gives reducedness after base change to each of these fields.

The Noetherian hypothesis belongs to the auxiliary theorem `isReduced_tensorProduct_of_isNoetherianRing_of_finiteDimensional`. `Algebra.IsSeparable` requires algebraicity.

References include Tag 030U, Tag 00I3, EGA 0 23.1.7, EGA IV 4.3.5, EGA IV 4.3.6 and EGA IV 6.7.6.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 23.1.7 | `isReduced_tensorProduct_of_isNoetherianRing_of_finiteDimensional` | partial |
| EGA | IV 4.3.5 | `isReduced_tensorProduct_of_isNoetherianRing_of_finiteDimensional` | special case |
| EGA | IV 4.3.6 | `isReduced_tensorProduct_of_isNoetherianRing_of_finiteDimensional` | special case |
| EGA | IV 6.7.6 | `isReduced_tensorProduct_of_isNoetherianRing_of_finiteDimensional` | special case |
| EGA | 0 23.1.7 | `isReduced_tensorProduct_of_finiteDimensional` | partial |
| EGA | IV 4.3.5 | `isReduced_tensorProduct_of_finiteDimensional` | special case |
| EGA | IV 4.3.6 | `isReduced_tensorProduct_of_finiteDimensional` | special case |
| EGA | IV 6.7.6 | `isReduced_tensorProduct_of_finiteDimensional` | special case |
| EGA | 0 23.1.7 | `isReduced_tensorProduct_of_isSeparable` | partial |
| EGA | IV 4.3.5 | `isReduced_tensorProduct_of_isSeparable` | special case |
| EGA | IV 4.3.6 | `isReduced_tensorProduct_of_isSeparable` | special case |
| EGA | IV 6.7.6 | `isReduced_tensorProduct_of_isSeparable` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/GeometricallyReduced/SeparableBaseChange.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 12 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
