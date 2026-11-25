# Finite-dimensional algebras over a field are Artinian

Module `StacksFrontier.RingTheory.Artinian.Basic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

`finite_dimensional_algebra_is_artinian` shows that a K-algebra R over a field K that is finite-dimensional over K is an Artinian ring. R is any ring with a K-algebra structure; it need not be commutative.

A comment of the file notes that Tags 00J7 and 00J8, finiteness of the set of maximal ideals and nilpotence of the Jacobson radical of an Artinian ring, are Mathlib's `IsArtinianRing.setOfPred_isMaximal_finite` and `IsArtinianRing.isNilpotent_jacobson_bot`.

The file's three module docstrings concern the decomposition of a ring with discrete spectrum, or of an Artinian ring, into the product of its localizations at its maximal ideals (Tags 00JA and 00JB), and each announces a main result on it; none of these is in the file, whose only declaration is the theorem above.

## References

Stacks Project Tag 00J6. A comment cites Tag 00J7 and Tag 00J8 for Mathlib results. EGA IV 2.5.8.8 (special case).

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00J6](https://stacks.math.columbia.edu/tag/00J6) | `finite_dimensional_algebra_is_artinian` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 2.5.8.8 | `finite_dimensional_algebra_is_artinian` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Artinian/Basic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 5 declarations of the source file 1 are kept. The 4 left out are not needed by the results for which the extract is made: `MaximalSpectrum.algebraMap_pi_bijective`, `Stacks.Artinian.ProductDecomposition.solution`, `isArtinianRing_iff_isFiniteLength_and_isNoetherianRing_and_toPiLocalization_bijective`, `nonempty_ringEquiv_pi_localization_and_isMaximal`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
