# Weak solutions and formally smooth solutions for valuation rings

Module `StacksFrontier.RingTheory.DiscreteValuationRing.Solution`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file defines what it means for a finite extension of fraction fields to eliminate ramification in an extension A → B of discrete valuation rings with compatible fraction fields K → L.

## Extensions and base-change data

`IsExtension` packages injectivity and localness of the algebra map. `ramificationIndex` gives the ramification index at the maximal ideals. `IsWeaklyUnramified` means ramification index one.

For finite K₁/K, `IntegralClosureBaseChange` specifies a presentation of the reduction of L ⊗[K] K₁, the integral closure A₁ of A in K₁, and the integral closure B₁ of B in the reduced tensor product. It records compatibility with both tensor inclusions and the maps on the integral closures, allowing the three rings to be given by any compatible carriers.

- `IntegralClosureBaseChange.IsWeakSolution` requires index one over A₁ at every maximal ideal q of B₁.
- `IntegralClosureBaseChange.IsSolution` requires each localized map from A₁ at the contraction of q to B₁ at q to be formally smooth for the maximal-ideal adic topology of the target.

## Ramification and discrete valuation rings

`ramificationIndex_characterization` identifies the index as the unique positive e with 𝔪_A B = 𝔪_Bᵉ and writes the image of any base uniformizer as a unit times the e-th power of any upstairs uniformizer. `weaklyUnramified_iff_map_maximalIdeal` gives the index-one case. Further lemmas identify the index with Mathlib's length-theoretic index and give multiplicativity and its consequences in towers.

`adjoinRoot_isDiscreteValuationRing` gives a discrete valuation ring from a monic polynomial with irreducible residue reduction over a discrete valuation ring, with maximal ideal extended from the base. `isDiscreteValuationRing_of_directed_union` gives a discrete valuation ring from a nonempty directed union of discrete valuation subrings with a common uniformizer, including the chain version.

The index calculation uses valuation and uniqueness of maximal-ideal powers. The root construction uses the residue polynomial to identify the unique maximal ideal, and the union argument extends unit-times-power factorization from the constituent rings.

These are library predicates. Weak solutions specify only the numerical index, and the formal smoothness predicate carries a universe for the test rings. The module docstring also lists a residue degree and a separable-solution predicate among the definitions; neither is in the file.

Tag 09E4 describes the extension and its invariants. Tag 09EM provides the base-change setup and Tag 09EN the solution terminology. The index statements refer to SGA 7 IX 10.3, SGA 7 IX 9.7 and SGA 7 VIII 7.3.5. The characterization and the index comparison specialize SGA 7 IX 10.3.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [09E4](https://stacks.math.columbia.edu/tag/09E4) | `IsExtension` |  |
| [09E4](https://stacks.math.columbia.edu/tag/09E4) | `ramificationIndex` |  |
| [09E4](https://stacks.math.columbia.edu/tag/09E4) | `IsWeaklyUnramified` |  |
| [09EN](https://stacks.math.columbia.edu/tag/09EN) | `IsWeakSolution` | (1), weak solution |
| [09EN](https://stacks.math.columbia.edu/tag/09EN) | `IsSolution.` | (2), solution |
| [09E4](https://stacks.math.columbia.edu/tag/09E4) | `ramificationIndex_characterization` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 7 IX 10.3 | `ramificationIndex` |  |
| SGA | 7 IX 9.7 | `ramificationIndex` |  |
| SGA | 7 IX 10.3 | `ramificationIndex_characterization` | special case |
| SGA | 7 IX 10.3 | `ramificationIndex_eq_ramificationIdx` | special case |
| SGA | 7 VIII 7.3.5 | `ramificationIndex_eq_ramificationIdx` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/Solution.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 53 declarations of the source file 51 are kept. The 2 left out are not needed by the results for which the extract is made: `IsDiscreteValuationRing.IntegralClosureBaseChange.IsSeparableSolution`, `IsDiscreteValuationRing.residueDegree`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 5 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
