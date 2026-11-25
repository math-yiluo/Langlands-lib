# Upper semicontinuity of relative dimension

Module `StacksFrontier.RingTheory.RelativeDimension.Semicontinuity`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a commutative R-algebra S and a natural number n, let Vₙ be the primes of S at which the relative dimension over R is at most n. The file proves that Vₙ is open for finite-type algebras.

- `Algebra.isOpen_setOf_relativeDimensionAt_le` proves that Vₙ is open in Spec S for a finite-type algebra S. More concretely, `Algebra.exists_notMem_ringKrullDim_fiber_le` finds a principal neighbourhood of any prime in Vₙ on which every fibre over Spec R has Krull dimension at most n.

For openness, the proof finds a principal localization near a prime of relative dimension m ≤ n that is quasi-finite over the m-variable polynomial ring. Base change to each residue field bounds the whole fibre by m, and invariance of the dimension at a point under open embeddings gives the pointwise bound on that neighbourhood.

The theorem uses natural number bounds on the pointwise function `Algebra.relativeDimensionAt`. The last two module docstrings state and prove that Vₙ is also quasi-compact when S is finitely presented (Stacks 00QJ); that result is not in the file, and the sections that follow those docstrings declare nothing.

Stacks Project Tag 00QH for openness. Tag 00QD gives the definition, and Tag 00QE and Tag 00QG give the quasi-finite argument.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00QH](https://stacks.math.columbia.edu/tag/00QH) | `isOpen_setOf_relativeDimensionAt_le` | The source's open neighbourhood `V` of a single prime `𝔮` with `dim_𝔮(S/R) = n` is pinned as the sublevel set `{𝔮 \| dim_𝔮(S/R) ≤ n}`, whose openness the remark following the lemma in the source gives as an equivalent reading of it; `dim_𝔮(S/R)` is `Algebra.relativeDimensionAt R 𝔮` (tag 00QD). See the module docstring. |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/RelativeDimension/Semicontinuity.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 12 declarations of the source file 6 are kept. The 6 left out are not needed by the results for which the extract is made: `Algebra.isCompact_isOpen_setOf_relativeDimensionAt_le`, `Stacks.RelativeDimension.CompactLocus.isCompact_setOf_relativeDimensionAt_le_of_isPushout`, `Stacks.RelativeDimension.CompactLocus.isCompact_setOf_relativeDimensionAt_le_of_presentation`, `Stacks.RelativeDimension.CompactLocus.setOf_relativeDimensionAt_le_eq_preimage`, `Stacks.RelativeDimension.CompactLocus.solution`, `Stacks.RelativeDimension.Semicontinuity.zero_le_of_ne_bot`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
