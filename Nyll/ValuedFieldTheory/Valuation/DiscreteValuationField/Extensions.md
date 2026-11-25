# Extensions of discretely valued fields: invariants and induced maps

Module `Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Extensions`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Setting: `L / K` a field extension, `base : DVF K` and `target : DVF L` discretely valued fields in the library's sense, with Mathlib's `HasExtension` saying that the valuation of `target` extends that of `base`. The file defines the degree, ramification index and residue degree, the maps induced on valuation rings, residue fields and units, and the predicates "unramified", "totally ramified" and "defectless". Through the projections `toDVF` the same definitions serve for Henselian and complete fields.

## Main definitions

- `degree`: `[L : K]` as `Module.finrank`.
- `ramificationIndex`: Mathlib's `Ideal.ramificationIdx'` of the maximal ideal of `O_L` over that of `O_K`; `residueDegree`: Mathlib's `inertiaDeg`.
- `integerMap : O_K → O_L`, `residueMap : k_K → k_L`, `unitMap : O_Kˣ → O_Lˣ`.
- `residueFieldEquivOfSurjective`, `residueUnitsEquivOfResidueMapSurjective`: the isomorphisms of residue fields and of their unit groups when the residue map is surjective.
- `HasRamificationIndexOne` (`e = 1`), with the abbreviation `IsUnramified`; `IsTotallyRamified` (`f = 1`); `IsDefectless` (`[L : K] = e · f`).

## Main results

- `integerMap_injective`; `algebraMap_mem_valuationSubring_iff`: `O_L ∩ K = O_K`; `integerMap_mem_maximalIdeal_iff` and `maximalIdeal_comap_integerMap_eq`: the maximal ideal of `O_L` pulls back to that of `O_K`; `integerMap_isUnit_iff`: units are preserved and reflected; `maximalIdeal_map_integerMap_ne_bot`: the ideal `𝔪_K O_L` is nonzero.
- `residueMap_injective`, with consequences: kernel zero, equality and the value `1` reflected, congruence criteria for residues, unit criteria through residues; `residueField_ringChar_eq_of_hasExtension`: the residue fields have the same characteristic.
- The induced map on residue units is injective, and bijective when the residue map is surjective.

## Points to watch

- `IsUnramified` only says `e = 1`; it does not ask for a separable residue extension, so it is weaker than the usual notion of an unramified extension.
- `IsTotallyRamified` only says `f = 1`.
- `IsDefectless` compares the global degree `[L : K]` with `e · f` for this one pair of valuations. When the base valuation has several extensions to `L`, this is stronger than the absence of defect, which concerns the sum over all extensions.
- Most results drop the hypothesis `FiniteDimensional K L`, and the definitions of `ramificationIndex`, `residueDegree` and the predicates do not use it either.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Extensions.lean`: the Lean file is the source byte for byte (SHA-256 `51e25a0f516662432cd9e1de58b4013563dda1ee14289019a21b956954294dbd`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
