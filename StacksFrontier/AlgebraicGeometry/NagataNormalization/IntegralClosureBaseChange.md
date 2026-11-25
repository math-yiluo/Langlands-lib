# Nagata base change along an integral closure

Module `StacksFrontier.AlgebraicGeometry.NagataNormalization.IntegralClosureBaseChange`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file studies the integral closure `B` of a Nagata domain `A` with fraction field `K` in a finite extension `L/K`.

`module_finite_integralClosure_of_isNagataRing` gives module finiteness of `B` over `A`, and `isNagataRing_integralClosure` shows that `B` is Nagata. The theorems `AlgebraicGeometry.isNagataScheme_spec_of_isNagataRing` and `isNagataScheme_of_isNagataRing` give Nagata-ness of the spectrum of a Nagata ring and of schemes locally of finite type over it. Thus `isNagataScheme_pullback_integralClosure` makes the fibre product of `X` and `Spec B` over `Spec A` Nagata for `X ⟶ Spec A` locally of finite type.

A Nagata domain is Japanese, giving module finiteness, and finite type permanence gives the Nagata property of `B`. Local finite type survives base change to `Spec B`.

The ring results allow independent universes for `A`, `K`, and `L`. The pullback places `A` and `L` in the scheme universe and allows `K` its own universe.

References are Tag 032T and Tag 035A.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/NagataNormalization/IntegralClosureBaseChange.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
