# ℤ̂ as the product of the p-adic integers

Module `Nyll.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerPrimeProduct`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file proves the Chinese remainder decomposition of the profinite integers: the canonical map from `ℤ̂` (the library's `ZHat`) to the product `∏_p ℤ_p` over all primes is an isomorphism of rings and a homeomorphism.

## Main definitions

- `ProfiniteIntegerPrimeProduct`: the product of Mathlib's `ℤ_[p]` over `Nat.Primes`, with the product topology.
- `zHatReductionRingHom`: reduction `ℤ̂ → ℤ/nℤ`, for `n > 0`, as a ring homomorphism; `zHatPadicReduction p n` is reduction modulo `p^n`, compatible in `n` (`zHatPadicReduction_compatible`).
- `zHatToPadicInt p`: the `p`-adic coordinate `ℤ̂ → ℤ_p`, obtained from these compatible reductions by `PadicInt.lift`.
- `zHatToProfiniteIntegerPrimeProduct`: the product of the coordinates.
- `zHatRingEquivProfiniteIntegerPrimeProduct`: the resulting ring isomorphism `ℤ̂ ≃+* ∏_p ℤ_p`.

## Main results

- `zHatToProfiniteIntegerPrimeProduct_injective`: an element of `ℤ̂` is determined by its `p`-adic coordinates; reduction modulo `n` is recovered from reductions modulo the prime-power factors of `n` through `ZMod.equivPi`.
- `continuous_zHatToPadicInt`, `continuous_zHatToProfiniteIntegerPrimeProduct`: the coordinate maps are continuous.
- `denseRange_intCast_profiniteIntegerPrimeProduct`: `ℤ` is dense in `∏_p ℤ_p`; a basic open set constrains finitely many coordinates, each modulo a prime power, and the finite Chinese remainder theorem finds an integer meeting all constraints.
- `zHatToProfiniteIntegerPrimeProduct_surjective`: the map is onto, since its range is compact, hence closed, and contains the dense image of `ℤ`.
- `isHomeomorph_zHatRingEquivProfiniteIntegerPrimeProduct`: the isomorphism is a homeomorphism, being a continuous bijection between compact Hausdorff spaces.
- `zHatToPadicInt_intCast`, `zHatToProfiniteIntegerPrimeProduct_intCast`: compatibility with the inclusion of `ℤ`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteIntegerPrimeProduct.lean`: the Lean file is the source byte for byte (SHA-256 `3c17f75c19f776bde485e675d34f5d85f8800dc06ca952bbb8287e403cdbe4b0`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
