# Topology on the units of a restricted product

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.RestrictedProductUnitsTopology`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `R i` be monoids indexed by `ι`, each with a topology (continuity of multiplication is not assumed), with distinguished submonoids `B i`. Mathlib's `RestrictedProduct.unitsEquiv` identifies, as groups, the units of the restricted product `Πʳ i, [R i, B i]` with the restricted product of the unit groups `(R i)ˣ` relative to the units of `B i`. This file shows that this identification is also a homeomorphism, the units on the left carrying Mathlib's topology of units (induced by `x ↦ (x, x⁻¹)`), when every `B i` is open. Applied to the adele ring of a number field, this describes the topology on the ideles.

## Main definitions and results

- `RestrictedProduct.inclusionMonoidHom`: for filters `𝓕 ≤ 𝓖`, the inclusion of the `𝓖`-restricted product into the `𝓕`-restricted product, as a monoid homomorphism.
- `RestrictedProduct.unitsEquivPrincipal T`: for the principal filter of a set `T`, the units equivalence is a topological group isomorphism, with no openness hypothesis.
- `RestrictedProduct.isOpenEmbedding_units_inclusion`: if every `B i` is open and `T` is cofinite, the inclusion of the principal stage into the cofinite restricted product induces an open embedding of unit groups.
- `RestrictedProduct.unitsContinuousMulEquiv`: if every `B i` is open, the units of the cofinite restricted product `Πʳ i, [R i, B i]` and the restricted product `Πʳ i, [(R i)ˣ, (B i)ˣ]` are isomorphic as topological groups.

## Proof

Continuity of the map is checked at each point `x`: `x` comes from the principal stage for the cofinite set of indices where its components are units of `B i`, and the open embedding of that stage transfers continuity from `unitsEquivPrincipal`. Continuity of the inverse uses Mathlib's criterion for maps out of a restricted product, one principal stage at a time.

## Points to watch

- The main result needs every `B i` open; only the principal-filter version is free of this hypothesis.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/RestrictedProductUnitsTopology.lean`: the Lean file is the source byte for byte (SHA-256 `d7c89ae84d78d676264ec62e24bf2c1729eac65ec43e90ac405636f9ac2aba5e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
