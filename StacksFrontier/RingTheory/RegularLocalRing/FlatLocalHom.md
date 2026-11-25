# Regularity along flat local homomorphisms

Module `StacksFrontier.RingTheory.RegularLocalRing.FlatLocalHom`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Regularity descends from the target of a flat local homomorphism. The file also defines the closed fibre of a local homomorphism and proves the dimension formula for flat ones.

For a local ring R and an R-algebra S, `ClosedFibre R S` is the quotient of S by the extension of the maximal ideal of R. When S and the structure map are local, the quotient is local (`ClosedFibre.instIsLocalRing`) with maximal ideal the image of the maximal ideal of S.

- `IsRegularLocalRing.of_flat_of_isLocalHom` assumes a flat local map from a Noetherian local ring R to a regular local ring S. It proves that R is regular local.
- For a local map between Noetherian local rings with flatness given as the explicit hypothesis `hflat`, `ringKrullDim_eq_add_ringKrullDim_closedFibre` gives dim S = dim R + dim of the closed fibre.

The dimension formula comes from going-down for flat maps and the height formula for primes lying over one another. Descent uses dimension shifting and faithfully flat descent of finite projectivity to bound the projective dimension of the source residue field by the dimension of S, then applies Serre’s criterion.

The descent statement explicitly requires locality and Noetherianity of the source. It allows independent ring universes by using a model of the base-changed residue field in the target module universe.

The first module docstring announces that a flat local map with regular source and regular closed fibre has a regular target, and outlines its proof; that result is not in the file.

Stacks Project, Tag 00ON and Tag 00OF. The descent proof uses Tag 00O1, Tag 00O5, Tag 00O7, and Tag 00OC. EGA 0 19.7.1 and SGA 1 III 1.7 concern the closed fibre, and EGA IV 6.1.1 and 6.1.2 concern the dimension formula. The descent result cites EGA IV 6.5.1, EGA 0 17.3.3, and SGA 1 I 9.1.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00OF](https://stacks.math.columbia.edu/tag/00OF) | `IsRegularLocalRing.of_flat_of_isLocalHom` | The source's \"local Noetherian and regular\" for `S` is the single class `IsRegularLocalRing S` (Definition 00KU), which extends `IsLocalRing` and `IsNoetherianRing`; the homomorphism is `algebraMap R S`, flat as `Module.Flat R S` and local as `IsLocalHom (algebraMap R S)`, the hypothesis pair of `Module.FaithfullyFlat.of_flat_of_isLocalHom`. See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 19.7.1 | `ClosedFibre` |  |
| EGA | I 3.7.2 | `ClosedFibre` | special case |
| EGA | IV 12.1.1.4 | `ClosedFibre` | special case |
| EGA | IV 6.1.3 | `ClosedFibre` |  |
| SGA | 1 III 1.7 | `ClosedFibre` |  |
| SGA | 3 XXVI 7.15 | `ClosedFibre` | special case |
| EGA | 0 1.0.7 | `ClosedFibre.mapMaximalIdeal_le` | local implies φ(m)⊆n |
| EGA | 0 6.6.2 | `ClosedFibre.instIsLocalRing` | partial |
| EGA | IV 21.10.1 | `ringKrullDim_eq_add_ringKrullDim_closedFibre` | partial |
| EGA | IV 6.1.1 | `ringKrullDim_eq_add_ringKrullDim_closedFibre` | Flat case of (6.1.1.1) |
| EGA | IV 6.1.2 | `ringKrullDim_eq_add_ringKrullDim_closedFibre` |  |
| EGA | IV 6.1.3 | `ringKrullDim_eq_add_ringKrullDim_closedFibre` | special case |
| EGA | IV 6.2.1 | `hasProjectiveDimensionLE_of_baseChange` | (ii) |
| EGA | 0 17.3.3 | `solution` |  |
| EGA | IV 6.5.1 | `solution` |  |
| SGA | 1 I 9.1 | `IsRegularLocalRing.of_flat_of_isLocalHom` | B regular ⇒ A regular |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/RegularLocalRing/FlatLocalHom.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 13 declarations of the source file 10 are kept. The 3 left out are not needed by the results for which the extract is made: `Submodule.spanRank_le_spanRank_add_spanRank_map_mkQ`, `isRegularLocalRing_of_flat_of_closedFibre`, `spanFinrank_maximalIdeal_le_add_spanFinrank_closedFibre`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 19 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text. The 16 on kept declarations are listed above; the 3 on a declaration left out are not in the file.
