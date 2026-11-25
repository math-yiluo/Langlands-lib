# The normalized ℤ-valued valuation of a local field

Module `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormalizedIntegerValuation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A nonarchimedean local field `K` carries its canonical valuation with values in an intrinsic value group. Some later arguments (the Kummer part of the local existence theorem, according to the module comment) use results stated for valuations with values in `ℤₘ₀ = WithZero (Multiplicative ℤ)`. This file transports the canonical valuation to `ℤₘ₀` and shows that the valuation ring, completeness and finiteness of the residue field carry over.

## Main definitions and results

- `localIntegerValuation K : Valuation K ℤₘ₀`: the canonical valuation followed by the order isomorphism `valueGroupWithZeroIsoInt K`. `localIntegerValuation_surjective`: it is onto `ℤₘ₀`.
- `localCompleteDVF_valuation_eq`: the valuation of the complete discretely valued field package `localCompleteDVF K` (built in an imported file) is the canonical valuation.
- `localIntegerValuation_valuationSubring_eq`: the new valuation has the same valuation ring. `localIntegerValuationSubringEquiv` is the corresponding ring isomorphism, the identity on elements, and it matches the maximal ideals (`localIntegerValuationSubringEquiv_map_maximalIdeal`).
- Instance `localIntegerValuation_isCompleteDiscrete`: the new valuation is rank-one discrete and its valuation ring is complete for the adic topology of its maximal ideal.
- Instance `localIntegerValuation_residueFinite`: its residue field is finite.
- `integerRing_moduleFinite_of_finite_separable`: for a finite separable extension `L/K` of nonarchimedean local fields whose canonical valuations are related by `Valuation.HasExtension`, the valuation ring of `L` is a finite module over that of `K`.

## Proofs

Everything is transported along the identity isomorphism of valuation rings, using that an order isomorphism preserves `≤ 1` and `< 1`. Nontriviality comes from a preimage of `exp (-1)`, and the value group is cyclic as a subgroup of `ℤ`. The finiteness theorem transports the corresponding statement for the complete-DVF packages along the equality of valuations.

## Points to watch

- `IsCompleteDiscrete` is a class of this library, not of Mathlib.
- `integerRing_moduleFinite_of_finite_separable` assumes separability, and takes the compatibility `Valuation.HasExtension` of the two canonical valuations as an instance argument rather than deriving it.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormalizedIntegerValuation.lean`: the Lean file is the source byte for byte (SHA-256 `0923fb9f51e6e3528c7a73d728b4b9a6814a7d297b850f1dd05b80613d949e7d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
