# Finite base change of local completions

Module `StacksFrontier.RingTheory.AdicCompletion.FiniteBaseChange`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a finite local homomorphism of commutative local rings with Noetherian source, completion at the maximal ideal can be computed by base change to the completed base.

`AdicCompletion.nonempty_algEquiv_tensorProduct_of_isLocalRing` assumes that A is Noetherian, A′ is local and finite as an A-module, and the structure map is local. It gives existence of an A′-algebra isomorphism from the tensor product of A′ with the maximal-ideal completion of A over A to the maximal-ideal completion of A′.

The proof applies the product formula for finite algebras, with A as its own localization at the maximal ideal (`IsLocalRing.isLocalization_atPrime_maximalIdeal`). The product has a single factor by the instance `IsLocalRing.unique_primesOver_maximalIdeal`: for a local integral map of local rings, a prime above the base maximal ideal is maximal by integrality, hence the maximal ideal of A′.

The module docstring also announces a locality criterion for integral closures in purely inseparable extensions, which is not in the file.

The file cites Tag 07N9 and Tag 0394, and SGA 1 III 1.6, of which the base-change result is a special case.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 1 III 1.6 | `nonempty_algEquiv_tensorProduct_of_isLocalRing` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/AdicCompletion/FiniteBaseChange.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 4 declarations of the source file 3 are kept. The 1 left out are not needed by the results for which the extract is made: `isLocalRing_integralClosure_of_isPurelyInseparable`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
