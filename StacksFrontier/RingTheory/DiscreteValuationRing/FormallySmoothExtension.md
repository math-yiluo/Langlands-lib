# Adic formal smoothness of discrete valuation ring extensions

Module `StacksFrontier.RingTheory.DiscreteValuationRing.FormallySmoothExtension`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For an extension A → B of discrete valuation rings, the file characterizes formal smoothness in the maximal-ideal-adic topology of B by the ramification index and the induced residue-field map.

`IsDiscreteValuationRing.formallySmooth_iff_weaklyUnramified_and_isSeparableExtension` proves that `RingHom.FormallySmoothNAdic` for A → B is equivalent to weak unramifiedness, meaning ramification index one, together with separability of κ(B) over κ(A). For a compatible tower A → B → C of DVR extensions, `formallySmoothNAdic_tower_bot` descends adic formal smoothness from A → C to A → B, and `formallySmoothNAdic_trans` composes adically formally smooth steps.

For the forward implication, formal smoothness base changes to the special fibre κ(A) ⊗ₐ B. Regularity as a local ring makes this fibre reduced, so the extended maximal ideal of A, a positive power of the maximal ideal of B, equals that maximal ideal. The special fibre then identifies with κ(B), where formal smoothness is equivalent to separability. The converse uses flatness of the DVR extension and `RingHom.FormallySmoothNAdic.of_flat_of_specialFibre`. The tower results combine the rules for weak unramifiedness with inheritance and transitivity of separability.

The residue-field algebra comes from the local map. The library's `Algebra.StacksIsSeparableExtension` also applies to nonalgebraic extensions.

References include Tag 09E7 for the characterization and Tag 07NQ, implication (2) ⇒ (3), for the flat special-fibre criterion.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [09E7](https://stacks.math.columbia.edu/tag/09E7) | `formallySmooth_iff_weaklyUnramified_and_isSeparableExtension` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/FormallySmoothExtension.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
