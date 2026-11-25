# Ramification index and the residue degree bound

Module `StacksFrontier.RingTheory.DiscreteValuationRing.RamificationIndex`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For maps of discrete valuation rings the file computes the ramification index from valuations, bounds the product of ramification index and residue degree by the fraction-field degree, and shows how the two indices multiply in towers.

`ramificationIdx` is the library's natural-valued definition given by `Ideal.ramificationIdx'` applied to the maximal ideals of two local rings. For an injective map of discrete valuation rings, `addVal_algebraMap_eq_ramificationIdx` identifies it with the upstairs valuation of a base uniformizer. `map_maximalIdeal_eq_maximalIdeal_pow_ramificationIdx` identifies the extended maximal ideal with the corresponding power upstairs. Localness gives positivity by `one_le_ramificationIdx`.

For an injective local map with compatible fraction fields K → L and finite L/K, `residueField_finite_and_ramificationIdx_mul_residueDegree_le_finrank` gives finiteness of the residue extension and e f ≤ [L : K].

`ramificationIdx_and_inertiaDeg_tower` gives multiplicativity of both indices for a compatible tower of injective local maps of discrete valuation rings.

For the bound, the proof computes the A-module length of B/𝔪_A B as e f and bounds it by the fraction-field degree. Multiplicativity uses the ideal-theoretic tower formulas with flatness over a discrete valuation ring.

The bound uses `Ideal.ramificationIdx` and the `Module.finrank` of the residue fields, and the tower formulas use `Ideal.ramificationIdx` and `Ideal.inertiaDeg`, while the local definition above uses the primed index.

The degree bound is Tag 09E5 and the tower formulas are Tag 0BRL. The index definition is referenced to SGA 7 VIII 7.3.5.

The module docstring also announces that e is a power of p for a purely inseparable extension in characteristic p; the file does not contain this result.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [09E5](https://stacks.math.columbia.edu/tag/09E5) | `residueField_finite_and_ramificationIdx_mul_residueDegree_le_finrank` |  |
| [0BRL](https://stacks.math.columbia.edu/tag/0BRL) | `ramificationIdx_and_inertiaDeg_tower` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 7 VIII 7.3.5 | `ramificationIdx` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/RamificationIndex.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 9 declarations of the source file 8 are kept. The 1 left out are not needed by the results for which the extract is made: `Stacks.DiscreteValuationRing.Ramification.ramificationIdx_eq_prime_pow_of_purelyInseparable`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
