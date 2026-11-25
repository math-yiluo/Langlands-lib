# The cyclic and uniformizer factors of Kˣ

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitFactors`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a complete discretely valued field `K` with finite residue field of order `q`, this file identifies two of the three factors in `Kˣ ≅ μ × U¹ × ℤ` as topological groups: the Teichmüller roots of unity `μ` are the cyclic group `ℤ/(q−1)` with the discrete topology, and the uniformizer factor is `ℤ`. The first principal units `U¹` are left unclassified. The statements are given both for the library's `CompleteDVF` and for a standard valuation `v : K → ℤᵐ⁰`.

## Main definitions and results

- General helpers: `continuousMulEquivOfCompactToT2` (a continuous algebraic isomorphism from a compact group to a Hausdorff one is a topological isomorphism, with an additive version), and products and swaps of topological isomorphisms.
- `residueRootsOfUnityContinuousMulEquivZMod`: `ℤ/(q−1) ≃ₜ* residueRootsOfUnityGroup F`, from cyclicity of the units of the finite residue field.
- `fieldUnitsContinuousMulEquivCyclicRootsPrincipalUnitsUniformizer`: `(ℤ/(q−1) × U¹) × ℤ ≃ₜ* Kˣ` for a chosen uniformizer, with the range-restricted valuation topology on `K`.
- `fieldUnitsContinuousMulEquivRootsPrincipalUnitsUniformizerOfWithZeroValuation`: the decomposition `fieldUnitDecompositionFactors F ≃ₜ* Kˣ`, transferred to the topology of `Valued.mk' v` for a complete discrete `ℤᵐ⁰`-valuation with finite residue field. It uses that this topology equals the range-restricted one (`valuedMk_uniformSpace_eq_mrangeRestrict`). The `ℤ/(q−1)` versions `residueRootsOfUnityContinuousMulEquivZModOfWithZeroValuation` and `fieldUnitsContinuousMulEquivCyclicRootsPrincipalUnitsUniformizerOfWithZeroValuation` follow.
- `fieldUnitsContinuousMulEquivUniformizerRootsPrincipalUnitsOfWithZeroValuation`: given any topological group `P` with `P ≃ₜ* U¹`, it produces `ℤ × (ℤ/(q−1) × P) ≃ₜ* Kˣ`.

## Points to watch

- The full structure theorem for `Kˣ` is not proved here: the last construction takes a topological classification of `U¹` as an argument.
- Topologies on `K` are introduced locally by `let`; the `ℤᵐ⁰` forms use the topology of `Valued.mk' v` and fix the value-group universe of the `CompleteDVF` to `0`.
- The cyclic factor is written `Multiplicative (ZMod (Nat.card F.residueField - 1))`, the additive group of residue classes under the `Multiplicative` tag, with natural subtraction.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/FieldUnitFactors.lean`: the Lean file is the source byte for byte (SHA-256 `d340bfe97e3e346a00883d9a051cb0b8df658594975c9f07cec2be81483ce860`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
