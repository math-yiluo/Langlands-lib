# Continuous lifting into complete adic rings

Module `StacksFrontier.RingTheory.FormallySmooth.AdicLifting`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Square-zero formal smoothness yields continuous lifts through closed quotients of complete adic rings when the quotient ideal has a power in the adic ideal.

`RingHom.FormallySmoothTop.exists_continuous_lift_of_isAdic` starts with f : R → S between linearly topologised rings, with the n-adic topology on S and the lifting property `RingHom.FormallySmoothTop` for f. Let A have the I-adic topology and be I-adically complete. For a closed ideal J of A with the bound `hJI` that Jᵗ ⊆ I for some t ≥ 1, a continuous map ψ : S → A/J compatible with a continuous map g : R → A admits a continuous lift φ : S → A. The lift extends g along f and reduces to ψ modulo J.

The proof iterates square-zero lifts into discrete quotients, using a pullback at each stage to preserve the reduction modulo J + Iᵏ. Adic completeness assembles the lifts, closedness of J gives agreement with ψ, and the power bound makes the lift continuous by forcing the image of a power of n into I.

The hypothesis `hf` tests continuous square-zero lifting on discrete rings in A’s universe.

## References

Stacks Project, Tag 07NJ.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [07NJ](https://stacks.math.columbia.edu/tag/07NJ) | `exists_continuous_lift_of_isAdic` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/FormallySmooth/AdicLifting.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
