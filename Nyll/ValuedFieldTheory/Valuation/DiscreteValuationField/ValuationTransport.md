# Pulling a valuation back along a field isomorphism

Module `Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ValuationTransport`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a valuation `v` on a field `K` and a ring isomorphism `e : L ≃+* K`, the file compares `v` with its pullback `v ∘ e` on `L`. It is meant for moving complete discrete valuation data from one copy of a field to another.

## Main results

- `valueGroup_comap_ringEquiv`: `v ∘ e` and `v` have the same value group (Mathlib's `MonoidWithZeroHom.valueGroup`).
- `isRankOneDiscrete_comap_ringEquiv` (an instance): if `v` is rank-one discrete, so is `v ∘ e`.
- `valuationSubringRingEquivOfComap`: the ring isomorphism from the valuation ring of `v ∘ e` to that of `v` induced by `e`.
- `valuationSubringRingEquivOfComap_mem_maximalIdeal_iff`, `maximalIdeal_map_valuationSubringRingEquivOfComap`, `maximalIdeal_comap_valuationSubringRingEquivOfComap`: this isomorphism matches the two maximal ideals, both by image and by preimage.

## Proofs

The value group statement compares the nonzero values taken by the two valuations, using surjectivity of `e`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ValuationTransport.lean`: the Lean file is the source byte for byte (SHA-256 `af1750f8484a27512efa6beaa05a943ac1e35d36ac089b18913305ab6fb4f26b`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
