# The Hilbert–Samuel degree

Module `StacksFrontier.RingTheory.HilbertSamuel.Defs`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file defines the Hilbert–Samuel degree from the eventual polynomial of cumulative quotient lengths.

## Definitions

For any ideal I of a commutative ring R and any R-module M, `Ideal.hilbertSamuelDegree` chooses a rational polynomial that computes the R-lengths of M / Iⁿ⁺¹M as finite values at all large n and takes its degree in `WithBot ℕ`. `Module.hilbertSamuelDegree` specializes to the maximal ideal of a local ring: it is the invariant d(M).

The degree definition has value −∞ both for the zero polynomial and as the fallback when there is no eventual polynomial. The module docstring still lists the length function χ, ideals of definition and the comparison of length functions for two ideals of definition; none of these is in the file.

## References

Stacks Project, Tag 00KA for the degree. The annotation cites Tag 00K9(2) for independence of the degree from the ideal of definition. EGA 0 16.2.3 concerns the degree.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00KA](https://stacks.math.columbia.edu/tag/00KA) | `Ideal.hilbertSamuelDegree` | Definition 00KA is the case `I = maximalIdeal R`, spelled `Module.hilbertSamuelDegree`. The definition is stated for an arbitrary ideal because that is the generality of the surrounding section, and because Lemma 00K9(2) is the assertion that this value is the same for all ideals of definition. |
| [00KA](https://stacks.math.columbia.edu/tag/00KA) | `Module.hilbertSamuelDegree` | The `d(M)` of the definition. Case (1) is not a separate branch: for `M = 0` the polynomial computing `χ_M` is `0`, whose degree is `-∞ = ⊥`, and conversely a computing polynomial of degree `-∞` forces `M = m ^ n M` for `n ≫ 0`, hence `M = 0` by Nakayama. See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 16.2.3 | `Ideal.hilbertSamuelDegree` |  |
| EGA | 0 16.2.3 | `Module.hilbertSamuelDegree` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/HilbertSamuel/Defs.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 7 declarations of the source file 2 are kept. The 5 left out are not needed by the results for which the extract is made: `IsIdealOfDefinition`, `IsIdealOfDefinition'`, `chi_change_ideal_of_definition`, `hilbertSamuel_chi`, `isIdealOfDefinition_iff`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
