# Adic continuity and square-zero lifting

Module `StacksFrontier.RingTheory.FormallySmooth.Adic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a discrete source and an adic target, continuous square-zero lifting is equivalent to lifting when the given map into the test quotient kills a positive power of the adic ideal.

`RingHom.formallySmoothTop_iff_formallySmoothNAdic` gives this equivalence for a homomorphism R → S when R is discrete and S has the n-adic topology. `RingHom.formallySmoothTop_of_formallySmoothNAdic` gives one direction, from the n-adic lifting property `RingHom.FormallySmoothNAdic` to continuous lifting `RingHom.FormallySmoothTop`, for any topological ring structure on R.

A map from S into a discrete ring is continuous exactly when it kills some nᵏ with k ≥ 1, and the base map out of discrete R is automatically continuous. If the map into A/J kills nᵏ, a lift sends nᵏ into J and kills n²ᵏ because J² = 0, so the lift is continuous.

Stacks Project, Tag 07EG.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [07EG](https://stacks.math.columbia.edu/tag/07EG) | `formallySmoothTop_iff_formallySmoothNAdic` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/FormallySmooth/Adic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
