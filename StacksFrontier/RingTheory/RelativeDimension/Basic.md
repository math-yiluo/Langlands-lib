# Computing relative dimension on fibres

Module `StacksFrontier.RingTheory.RelativeDimension.Basic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a commutative R-algebra S, these results compute the relative dimension at a prime on the spectrum of the fibre ring and show its invariance under principal localization.

- `Algebra.relativeDimensionAt_eq_localKrullDim` identifies the relative dimension at a prime 𝔮 of S over 𝔭 with the topological local Krull dimension of the spectrum of `κ(𝔭) ⊗[R] S` at a prime 𝔔 contracting to 𝔮. `Ideal.Fiber.exists_comap_includeRight_eq` supplies such a 𝔔.
- `Algebra.relativeDimensionAt_comap_eq` gives equality of relative dimensions at a prime of a principal localization of S and at its contraction to S, using the compatible R-algebra structures.

The first computation uses the homeomorphism from the topological fibre to the fibre spectrum. Principal localization restricts to an open embedding on fibres.

The module docstring also announces the relative dimension of an algebra all of whose fibres have one dimension d; that result is not in the file, which keeps only the heading of its section.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/RelativeDimension/Basic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 8 declarations of the source file 4 are kept. The 4 left out are not needed by the results for which the extract is made: `Algebra.relativeDimensionAt_congr`, `Algebra.relativeDimensionAt_eq_topologicalKrullDimAt_fiber`, `Algebra.relativeDimension_eq_of_forall_topologicalKrullDim_fiber`, `Ideal.Fiber.exists_mem_isUnit_includeRight_of_one_mem_map`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
