# Valuation rings, residue fields and valuations of the universe-0 model of a local field

Module `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkResidueTransport`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A nonarchimedean local field `K` in any universe has a copy `Shrink.{0} K` in universe `0`, carrying the valuative relation transported along the ring isomorphism `Shrink.ringEquiv K : Shrink.{0} K ≃ K` (both set up in imported files). This file shows that this isomorphism respects the integral structure: it restricts to the valuation rings, descends to the residue fields, carries principal units to principal units, and preserves the normalized valuation.

## Main definitions and results

- `shrinkLocalField_mem_integer_iff`: `x` lies in `𝒪[Shrink.{0} K]` exactly when its image lies in `𝒪[K]`.
- `shrinkIntegerRingEquiv : 𝒪[Shrink.{0} K] ≃+* 𝒪[K]`, the restriction, agreeing with `Shrink.ringEquiv K` on elements.
- `shrinkResidueFieldEquiv : 𝓀[Shrink.{0} K] ≃+* 𝓀[K]`, compatible with reduction; `shrinkResidueField_card`: the residue fields have the same cardinality.
- `shrinkIntegerUnitsToFieldUnits`: the inclusions of integral units into field units commute with the isomorphisms.
- `fieldPrincipalUnits_map_shrink`: for every `n`, the field principal-unit subgroup of level `n` of `Shrink.{0} K` maps onto that of `K`.
- `valuationMap_shrinkRingEquiv`: the normalized additive valuation of `K` at the image of `x` equals that of `Shrink.{0} K` at `x`.

## Proofs

The valuation statement writes `x` as an integral unit times a power of the inverse uniformizer (`uniformizerUnitFactor`); the image of a uniformizer is irreducible, hence its inverse has value `1` in `K`, and units have value `0`.

## Points to watch

- Every statement fixes the instances `smallLocalField K`, `shrinkLocalFieldValuativeRel K` and, for the valuation, `shrinkLocalField_isNonarchimedeanLocalField K` by `let` inside the statement; they concern this particular model, not an arbitrary small copy.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ShrinkResidueTransport.lean`: the Lean file is the source byte for byte (SHA-256 `d5d16bb26ed29a6fda3c1157d30e4ee5c8e715cd9d9525ee48e7159faee9ddcd`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
