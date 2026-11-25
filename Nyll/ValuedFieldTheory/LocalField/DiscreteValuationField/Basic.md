# Local fields with a chosen discrete valuation

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file introduces the library's notion of a local field: a field `K` together with a chosen complete discrete valuation whose residue field is finite. It then works out the arithmetic of the residue characteristic `p`: which integers are units or lie in the maximal ideal, which rationals lie in the valuation ring, and how the valuation restricted to `ℚ` compares with the `p`-adic valuation.

## Main definitions and results

- `LocalField K` extends the complete discretely valued field package `CompleteDVF K` by the instance `residueFinite`, finiteness of the residue field. The abbreviations `residueField`, `valuationSubring`, `maximalIdeal` and `residueMap` pass through to the package.
- `valuationSubring_isDiscreteValuationRing`, `henselianRing`, `exists_uniformizer`: the valuation ring is a DVR, is Henselian for its maximal ideal, and has a uniformizer; all three are inherited from `CompleteDVF`.
- `residueCharacteristic` is `ringChar` of the residue field. It is nonzero and prime (`residueCharacteristic_prime`), and instances register `CharP` and `Fact p.Prime`.
- For an integer or natural number `n`: `n` lies in the maximal ideal, equivalently has valuation `< 1`, iff `p ∣ n`; it is a unit of the valuation ring, and then has valuation `1`, iff `p ∤ n` (`intCast_mem_maximalIdeal_iff_residueCharacteristic_dvd`, `isUnit_intCast_iff_not_residueCharacteristic_dvd` and their variants in `K`). Every integer has valuation `≤ 1`.
- A rational `q` whose denominator is prime to `p` has the valuation of its numerator, hence lies in the valuation ring. Under `[CharZero K]` the converse holds (`valuation_ratCast_le_one_iff_not_residueCharacteristic_dvd_den`); consequently the preimage of the valuation ring under `ℚ → K` is the `p`-adic valuation ring of `ℚ` (`ratCast_preimage_valuationSubring_eq_padicValuationSubring`), and the restricted valuation is equivalent to `Rat.padicValuation p` (`ratCast_valuation_isEquiv_padicValuation`).
- If `K` has characteristic `p ≠ 0`, the residue field has characteristic `p` and `residueCharacteristic = p` (`residueCharacteristic_eq_of_charP`).
- A finite field that is an algebra over the residue field is algebraic and separable over it; in particular `residueExtension_isSeparable` for the residue fields of two local fields.

For the converse on rationals: if `p` divides the reduced denominator it does not divide the numerator, so the numerator has valuation `1` and the denominator valuation `< 1`, forcing valuation `> 1`.

## Points to watch

- `LocalField` is the library's own structure, carrying the valuation as data; it is not Mathlib's topology-first local field class, which is only imported. It has two universe parameters, the second being that of the underlying `CompleteDVF`.
- All statements concern the chosen valuation `F.toCompleteDVF.valuation`. The comparison on `ℚ` is equivalence of valuations, not equality, and it needs `CharZero K`.
- `residueExtension_isSeparable` uses only finiteness: the algebra between the residue fields is an arbitrary instance, not one induced by a map of local fields.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Basic.lean`: the Lean file is the source byte for byte (SHA-256 `ebbf682b624a5fb2e0cb863ec24d85bac4a0cabd220303d55a77899175e0d1ef`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
