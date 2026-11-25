# Quotients of localizations at prime ideals

Module `StacksFrontier.RingTheory.Localization.AtPrimeQuotient`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Taking a quotient by an extended ideal commutes with localization at a prime that comes from the quotient ring.

`isLocalization_atPrime_quotient` takes a commutative ring B, a prime 𝔫 of B, a model B𝔫 of its localization, and an ideal J of B. Given a prime 𝔮 of B/J whose inverse image is 𝔫, it shows that B𝔫/JB𝔫 is a localization of B/J at 𝔮.

The proof uses surjectivity of the quotient map to identify the image in B/J of the complement of 𝔫 with the complement of 𝔮. It then invokes Mathlib’s quotient localization instance.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Localization/AtPrimeQuotient.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
