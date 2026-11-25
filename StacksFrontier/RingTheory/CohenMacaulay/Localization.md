# Localization of Cohen–Macaulay modules and rings

Module `StacksFrontier.RingTheory.CohenMacaulay.Localization`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Cohen–Macaulayness passes from a finite module over a Noetherian local ring to its localizations at primes in the support. The ring case follows by taking the module to be the ring itself.

## Main results

- `Module.depth_eq_supportDim_of_isLocalizedModule` starts with a finite R-module M over a Noetherian local ring R such that the depth of M at the maximal ideal of R equals the dimension of the support of M. Given a prime p and a nonzero localization Mₚ over Rₚ, it proves the corresponding equality over Rₚ.
- `Module.IsMaximalCohenMacaulay.of_isLocalization_atPrime` proves that localizing a Noetherian local Cohen–Macaulay ring at any prime yields a Cohen–Macaulay local ring. The support of Rₚ over itself is its whole spectrum.

The module proof combines the depth bound under localization with the inequality dim Supp(Mₚ) + dim(R/p) ≤ dim Supp(M), obtained by bounding the two terms by height and coheight in the support. Cancelling the finite term dim(R/p) gives the lower bound on local depth, and the general depth bound gives the reverse inequality.

The assumption `Nontrivial Mₚ` expresses that p belongs to the support of M. The zero module has depth ∞ and support dimension −∞ under these conventions. Both the ring and module localizations are specified by their universal properties using `IsLocalization.AtPrime` and `IsLocalizedModule`.

## References

Tag 0AAG is the module statement and Tag 00NB is the ring case. The depth comparisons use Tag 0FCC and Tag 00LK. See also EGA 0 16.5.10, EGA 0 16.5.13, and EGA IV 6.11.5.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0AAG](https://stacks.math.columbia.edu/tag/0AAG) | `depth_eq_supportDim_of_isLocalizedModule` | Cohen–Macaulayness is spelled out as `depth_𝔪(N) = dim Supp(N)`, the equation \   Definition 00N3 unfolds to, there being no predicate for it in this library yet; the \   localization is presented by `IsLocalization.AtPrime` and `IsLocalizedModule`; and `𝔭` is \   required to lie in `Supp(M)`, spelled `Nontrivial Mₚ`, without which the conclusion is false \   for the source's own conventions. See the module docstring. |
| [00NB](https://stacks.math.columbia.edu/tag/00NB) | `Module.IsMaximalCohenMacaulay.of_isLocalization_atPrime` | Cohen-Macaulayness of a Noetherian local ring is the predicate `Module.IsMaximalCohenMacaulay S S`, i.e. `depth_{𝔪_S}(S) = dim S` (Definition 00N8); the localization is an abstract `IsLocalization.AtPrime`. See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 16.5.10 | `supportDim_add_ringKrullDim_quotient_le_supportDim` | partial |
| EGA | 0 16.5.10 | `depth_eq_supportDim_of_isLocalizedModule` |  |
| EGA | 0 16.5.13 | `depth_eq_supportDim_of_isLocalizedModule` | forward direction |
| EGA | 0 16.5.10 | `Module.IsMaximalCohenMacaulay.of_isLocalization_atPrime` | (i) for M = A |
| EGA | 0 16.5.13 | `Module.IsMaximalCohenMacaulay.of_isLocalization_atPrime` | partial |
| EGA | IV 6.11.5 | `Module.IsMaximalCohenMacaulay.of_isLocalization_atPrime` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/CohenMacaulay/Localization.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 6 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
