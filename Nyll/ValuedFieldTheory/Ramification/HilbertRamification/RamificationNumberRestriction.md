# Ramification numbers of a quotient

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RamificationNumberRestriction`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite Galois extension with group G, with discrete valuations `base` on K and `target` on L (the library's `DVF` structures), `target` extending `base`, and valuation ring O_L. For a normal subgroup H with fixed field M = L^H, the file proves without completeness that the ramification number of the restriction σ|_M is, up to the factor e(L/M), the sum of the ramification numbers over the coset σH.

## Definitions

- `cosetRamificationNumberSum huniq H σ z`: the sum over τ in H of the ramification numbers i_z(στ) at a given element z of O_L.
- `intrinsicCosetRamificationNumberSum huniq H σ`: the same sum for the intrinsic ramification number, which uses an internally chosen generator.

## Results

- `addVal_cosetGeneratorDisplacementProduct`: the additive valuation of the product of στ(z) − z over τ ∈ H is `cosetRamificationNumberSum`.
- `cosetRamificationNumberSum_eq_intrinsic`: if z generates O_L over O_K, the coset sum at z equals the intrinsic coset sum.
- `ramificationIndex_nsmul_fixedFieldRamificationNumber_eq_cosetSum`: for every σ in G, e(L/M) times the ramification number of σ|_M in M/K equals the sum over τ ∈ H of the ramification numbers of στ in L/K, as an identity in ℕ∞, with e(L/M) given by `fixedFieldRamificationIndex` and the ramification number in M/K by `fixedFieldRamificationNumber`. For σ in H both sides are infinite.

## Proof

By an earlier file, the coset product generates the extension to O_L of the displacement ideal of σ|_M, which is principal in the discrete valuation ring of M. Its valuation in O_L is e(L/M) times its valuation in M, and the valuation of a product is the sum of the valuations.

## Watch for

- Unique extension of the valuation is the explicit hypothesis `huniq : DVF.HasUniqueValuationExtension base target`. The intrinsic statements also assume the residue extension separable.
- The identity is stated without division, as a multiple in ℕ∞. The fixed-field ramification number is defined through the displacement ideal of M's valuation ring, not through a generator of that ring.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RamificationNumberRestriction.lean`: the Lean file is the source byte for byte (SHA-256 `b70754fb5bcf8856874cd8f24d212e7538c1cdeae181a27d299bda747f19a6bc`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
