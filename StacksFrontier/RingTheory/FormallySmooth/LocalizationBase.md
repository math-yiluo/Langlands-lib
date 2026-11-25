# Adic formal smoothness after localising the base

Module `StacksFrontier.RingTheory.FormallySmooth.LocalizationBase`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Localising the base of a ring map leaves the local homomorphism at a prime isomorphic to the local homomorphism obtained from the original base.

`RingHom.formallySmoothNAdic_localRingHom_of_isLocalization` takes a tower R → R′ → S where R′ is a localisation of R, and a prime q of S. Write p and p′ for its contractions. If R′ₚ′ → S_q is formally smooth for the maximal-ideal-adic topology of S_q, then Rₚ → S_q has the same property. This is the direction used for the integral closures in the reduced-fibre argument associated with Tag 09EN(2).

The proof identifies R′ₚ′ as a localisation of R at p and checks that the resulting source isomorphism commutes with the maps to S_q. It then applies `RingHom.FormallySmoothNAdic.of_arrowEquiv_of_map_eq` with the identity on S_q.

Stacks Project, Tag 0307 and Tag 09IL.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/FormallySmooth/LocalizationBase.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
