# Integral closure after localising the base

Module `StacksFrontier.RingTheory.FormallySmooth.IntegralClosureBaseLocalization`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Localising the base ring commutes with taking integral closure inside a fixed ambient ring when the inverted elements act as units there.

`isLocalization_integralClosure_of_forall_isUnit` identifies the integral closure of a localisation A′ of A in K₁ as the localisation of the integral closure of A in K₁ at the images of the denominators. It assumes compatible algebra structures and that the denominators become units in K₁. `isLocalization_integralClosure_primeCompl` verifies the unit condition when A is a domain, A′ localises it at a prime, and K₁ extends its fraction field K.

`RingHom.formallySmoothNAdic_localRingHom_integralClosure_primeCompl` assumes a compatible algebra T over both closures and a prime q of T. Formal smoothness for the maximal-ideal topology on T_q transfers from the map out of the localised closure of A′ to the map out of the localised closure of A. The proof applies transport along a base localisation. Here K, K₁, and T share a universe.

Stacks Project, Tag 09EN, Tag 0307, and Tag 09IL.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/FormallySmooth/IntegralClosureBaseLocalization.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
