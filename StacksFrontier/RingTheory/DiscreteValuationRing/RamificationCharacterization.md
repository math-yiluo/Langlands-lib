# Weak unramifiedness and the extended maximal ideal

Module `StacksFrontier.RingTheory.DiscreteValuationRing.RamificationCharacterization`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For an extension A → B of discrete valuation rings, `map_maximalIdeal_eq_iff_isWeaklyUnramified` characterizes weak unramifiedness by 𝔪_A B = 𝔪_B.

The proof reads both directions off `ramificationIndex_characterization`, by which 𝔪_A B = 𝔪_Bᵉ for the ramification index e and e is the only exponent n ≥ 1 with 𝔪_A B = 𝔪_Bⁿ. The statement uses the library's `IsExtension` for the injective local algebra map and `IsWeaklyUnramified` for index one.

The module docstring also announces the uniqueness of e and descriptions by uniformizers as results of the file; they are not in it.

Tag 09E4 is the reference for weak unramifiedness.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/RamificationCharacterization.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 4 declarations of the source file 1 are kept. The 3 left out are not needed by the results for which the extract is made: `IsDiscreteValuationRing.exists_unit_algebraMap_eq_mul_pow`, `IsDiscreteValuationRing.isWeaklyUnramified_iff_exists_unit_algebraMap_eq_mul`, `IsDiscreteValuationRing.ramificationIndex_unique`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
