# Relative algebraic closure

Module `StacksCore.FieldTheory.AlgebraicClosure`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

On the algebraic closure `k̄` of a field `k` inside an extension `K` (Mathlib's `algebraicClosure k K`).

- `finiteDimensional_algebraicClosure_of_essFiniteType`: an instance saying that if `K/k` is essentially of finite type (`Algebra.EssFiniteType`), then `k̄` is finite-dimensional over `k`.

A transcendence basis `s` of `K` over `k̄` is also one over `k`. Then `K` is essentially of finite type and algebraic over `k(s)`, hence finite over it, so `k̄(s)` is finite over `k(s)`; the library's `MvRatFunc.finite_iff` turns this into finiteness of `k̄` over `k`.

## References

Tag 037J (on `finiteDimensional_algebraicClosure_of_essFiniteType`). The table of tags below also attaches part (1) of Tag 037I to Mathlib's `algebraicClosure` and `mem_algebraicClosure_iff`.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [037J](https://stacks.math.columbia.edu/tag/037J) | `finiteDimensional_algebraicClosure_of_essFiniteType` |  |
| [037I](https://stacks.math.columbia.edu/tag/037I) | `algebraicClosure` | (1) |
| [037I](https://stacks.math.columbia.edu/tag/037I) | `mem_algebraicClosure_iff` | (1), correctness |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksCore/FieldTheory/AlgebraicClosure.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 3 declarations of the source file 1 are kept. The 2 left out are not needed by the results for which the extract is made: `IsAlgClosedIn`, `instIsAlgClosedSubtypeMemIntermediateFieldAlgebraicClosure_stacksCore`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
