# Naturality of norm-residue symbols for fixed fields

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldNormResidueNaturality`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Fix a Galois extension `Ω/k`. The abstract class formation on the units of `Ω` produces norm-residue symbols indexed by closed subgroups of `Gal(Ω/k)`. This file transports two naturality properties of these symbols, norm against restriction and inclusion against transfer, to the actual fixed fields in `Ω` and their actual relative Galois groups, and then specializes them to the separable closure of a nonarchimedean local field.

## Main definitions

- `abstractFixedFieldNormResidueSymbol`: for closed subgroups `L ≤ K` with `L` normal of finite index in `K` and `K` of finite index in `Gal(Ω/k)`, the map from the units of the fixed field of `K` to the abelianized Galois group of the fixed field of `L` over it, built from the class-formation symbol `D.normResidueSymbol` and the canonical identifications.
- `abstractFixedFieldUnitsInclusion`, `abstractFixedFieldNormUnits`: inclusion of units and the ordinary field norm on units between fixed fields.
- `abstractFixedFieldAbelianizedRestriction`, `abstractFixedFieldAbelianizedTransfer`: restriction and transfer between abelianized relative Galois groups, transported from the subgroup side.

## Main results

- `abstractFixedFieldNormResidueSymbol_norm_restriction`: for a square of fixed fields with both horizontal extensions finite Galois and the vertical base extension finite, restriction after the upper symbol equals the lower symbol after the field norm. The base extension need not be normal. Requires `Ω` separably closed.
- `abstractFixedFieldNormResidueSymbol_transfer_inclusion`: for a tower whose total extension is finite Galois, transfer after the base symbol equals the intermediate symbol after inclusion of units.
- `LocalFixedFieldNormRestrictionSquare.norm_restriction_commutes` and `LocalFixedFieldTransferTower.transfer_inclusion_commutes`: the same statements for structures bundling such squares and towers in `SeparableClosure k`, with the symbols of the canonical local class formation (`localResidueDatum`, `localHenselianValuation`, `separableClosureUnits_isClassFormation`).

## Proofs

Each identity is the corresponding naturality statement of the abstract reciprocity theory, rewritten through the unit and Galois identifications; the norm case also uses that the abstract relative norm agrees with the field norm on units.

## Points to watch

- In the general theorems the class field axiom is a hypothesis `hcf : SatisfiesClassFieldAxiom (galoisAmbientUnitsRep k Ω)`, together with degree data `D` and valuation data `v`; only the local specializations supply them.
- Normality of the extension subgroups and finiteness of the corresponding quotients are carried as instance arguments.
- The fields `k` and `Ω` are taken in `Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldNormResidueNaturality.lean`: the Lean file is the source byte for byte (SHA-256 `05d47171c1bade77835d9eb12994cec8304b5bf090c9c693b0a58f0602a82051`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
