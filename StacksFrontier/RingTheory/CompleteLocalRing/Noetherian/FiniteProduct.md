# Finite algebras over Noetherian complete local rings

Module `StacksFrontier.RingTheory.CompleteLocalRing.Noetherian.FiniteProduct`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A module-finite algebra over a Noetherian complete local ring decomposes as a finite product of Noetherian complete local rings.

- `IsNoetherianCompleteLocalRing` bundles Noetherianity, locality, and completeness and separatedness for powers of the maximal ideal.
- `finite_isProduct_isNoetherianCompleteLocalRing` gives a ring isomorphism from a finite R-algebra S to a product indexed by a finite type `Fin m`, with each factor Noetherian complete local.
- `isArtinianRing_quotient_map_maximalIdeal` shows that the closed fibre S/𝔪S of a finite algebra over a local ring is Artinian.

A finite algebra S is first shown complete for 𝔪S. Orthogonal idempotents summing to one in the Artinian closed fibre S/𝔪S then lift through square-zero quotients using that completeness, and cofinality of ideal powers gives completeness for each local factor’s own maximal ideal.

The product factors are in the universe of S, and the finite index may be empty when S is the zero ring. The module docstring also announces that the quotient of a Noetherian complete local ring by a proper ideal is again one; that result is not in this file.

## References

The main result carries Tag 0325. The table of references below records EGA 0 7.1.2, EGA 0 7.1.9, EGA III 5.1.1, SGA 2 X 2.1, SGA 3 XX 1.10, SGA 7 VI 1.15, and SGA 7 VI 5.11 for the complete local ring notion. It cites EGA 0 7.4.2, EGA 0 7.7.8, EGA 0 7.8.1, and EGA IV 18.5.16 for finite-algebra completeness, and EGA I 6.2.2 for the Artinian decomposition. For the finite product it records EGA 0 22.3.1, EGA IV 18.5.9 (ii), EGA IV 5.4.3, SGA 1 III 1.4, SGA 3 VIIB 0.1.1, SGA 3 XV 1.5, SGA 3 XV 3.9, and SGA 4 VIII 4.1 (i).

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0325](https://stacks.math.columbia.edu/tag/0325) | `finite_isProduct_isNoetherianCompleteLocalRing` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 7.1.2 | `IsNoetherianCompleteLocalRing` | special case |
| EGA | 0 7.1.9 | `IsNoetherianCompleteLocalRing` | special case |
| EGA | III 5.1.1 | `IsNoetherianCompleteLocalRing` | special case |
| SGA | 2 X 2.1 | `IsNoetherianCompleteLocalRing` |  |
| SGA | 3 XX 1.10 | `IsNoetherianCompleteLocalRing` |  |
| SGA | 7 VI 1.15 | `IsNoetherianCompleteLocalRing` | partial |
| SGA | 7 VI 5.11 | `IsNoetherianCompleteLocalRing` | partial |
| EGA | 0 7.4.2 | `finite_isAdicComplete_of_complete` | special case |
| EGA | 0 7.7.8 | `finite_isAdicComplete_of_complete` | A = B |
| EGA | 0 7.8.1 | `finite_isAdicComplete_of_complete` | special case |
| EGA | IV 18.5.16 | `finite_isAdicComplete_of_complete` | special case |
| EGA | I 6.2.2 | `S3a_artinian_coi_fin` | special case |
| SGA | 3 VIIB 0.1.1 | `S3a_artinian_coi_fin` | partial |
| EGA | 0 22.3.1 | `finite_isProduct_isNoetherianCompleteLocalRing` | special case |
| EGA | IV 18.5.9 | `finite_isProduct_isNoetherianCompleteLocalRing` | (ii), special case |
| EGA | IV 5.4.3 | `finite_isProduct_isNoetherianCompleteLocalRing` | special case |
| SGA | 1 III 1.4 | `finite_isProduct_isNoetherianCompleteLocalRing` | special case |
| SGA | 3 VIIB 0.1.1 | `finite_isProduct_isNoetherianCompleteLocalRing` | special case |
| SGA | 3 XV 1.5 | `finite_isProduct_isNoetherianCompleteLocalRing` | partial |
| SGA | 3 XV 3.9 | `finite_isProduct_isNoetherianCompleteLocalRing` |  |
| SGA | 4 VIII 4.1 | `finite_isProduct_isNoetherianCompleteLocalRing` | (i), special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/CompleteLocalRing/Noetherian/FiniteProduct.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 30 declarations of the source file 27 are kept. The 3 left out are not needed by the results for which the extract is made: `isPrecomplete_map_of_surjective`, `quotient_isNoetherianCompleteLocalRing`, `sub_mem_pow_of_succ_sub_mem_pow`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 21 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
