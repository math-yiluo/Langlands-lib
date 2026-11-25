# Dimension, Hilbert–Samuel degree, and systems of parameters

Module `StacksFrontier.RingTheory.HilbertSamuel.DimensionTheorem`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a commutative Noetherian local ring R, the Krull dimension is the degree of the Hilbert–Samuel polynomial of R and the minimum number of generators of an ideal whose radical is the maximal ideal 𝔪.

## Results

`IsLocalRing.ringKrullDim_eq_tfae`, proved by `Stacks.HilbertSamuel.DimensionTheorem.solution`, states that the following three conditions on a natural number d are equivalent.

1. The Krull dimension of R is d.
2. There are fixed integers a(i) for i ≤ d, with a(d) ≠ 0, such that for all large n the R-length of R / 𝔪ⁿ⁺¹ is finite and equals the sum of a(i) times (n choose i) over i ≤ d.
3. The least value of `Submodule.spanFinrank` among ideals with radical 𝔪 is d. Thus a system of parameters of size d exists, and every system of parameters has at least d elements.

The helpers identify the binomial condition with `Module.hilbertSamuelDegree R R` and transport quotient lengths from a quotient ring to R. Krull’s height theorem gives the comparison with the number of generators.

To bound dimension by degree, the proof passes to the domain obtained by quotienting by the first prime of a longest chain. Killing a nonzero element of its maximal ideal strictly lowers the degree by short exact sequence additivity, and lowers dimension by at most one. For the reverse bound, prime avoidance gives an element whose quotient has strictly smaller dimension. A quotient-length inequality bounds the original function by a partial sum of the quotient’s function, raising the degree bound by one. In dimension zero the nilpotent maximal ideal gives an eventually constant positive length.

The result concerns R as a module over itself. The local-ring instance supplies nontriviality, and the proof identifies both dimension and degree with natural numbers.

## References

Stacks Project, Tag 00KQ, with Tag 00KA for the degree, Tag 00K8 for eventual polynomiality, and Tag 00KC for short exact sequences. EGA 0 16.2.1, 0 16.2.3.2, 0 16.2.5 and IV 5.1.6.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00KQ](https://stacks.math.columbia.edu/tag/00KQ) | `IsLocalRing.ringKrullDim_eq_tfae` | Items (1)-(3); see the module docstring for the form of (2) and (3). |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 16.2.1 | `Computes.ne_zero_self` | special case |
| EGA | 0 16.2.3.2 | `ringKrullDim_le_of_hilbertSamuelDegree_le` | special case |
| EGA | 0 16.2.5 | `IsLocalRing.ringKrullDim_eq_tfae` | local case |
| EGA | IV 5.1.6 | `IsLocalRing.ringKrullDim_eq_tfae` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/HilbertSamuel/DimensionTheorem.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 37 declarations of the source file 36 are kept. The 1 left out are not needed by the results for which the extract is made: `Stacks.HilbertSamuel.DimensionTheorem.binomSum_degree_le`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 4 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
