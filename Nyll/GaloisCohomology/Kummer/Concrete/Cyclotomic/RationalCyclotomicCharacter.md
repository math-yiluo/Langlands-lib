# The cyclotomic character of ℚ(μ∞)

Module `Nyll.GaloisCohomology.Kummer.Concrete.Cyclotomic.RationalCyclotomicCharacter`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file defines the cyclotomic character of `Gal(ℚ(μ∞)/ℚ)` with values in `ℤ̂ˣ`, as the product over all primes of Mathlib's `p`-adic cyclotomic characters, for the actual field `rationalCyclotomicField` (the field `ℚ(μ∞)` inside a separable closure of `ℚ`).

## Main definitions and results

- Instance `rationalCyclotomicField_hasEnoughRootsOfUnity`: `ℚ(μ∞)` contains a primitive `n`-th root of unity for every `n ≠ 0`.
- `rationalCyclotomicCharacterPrimeProduct`: the continuous homomorphism `Gal(ℚ(μ∞)/ℚ) → ∏_p ℤ_pˣ` whose `p`-th coordinate is Mathlib's `cyclotomicCharacter` at `p` (`rationalCyclotomicCharacterPrimeProduct_apply`).
- `rationalCyclotomicCharacterPrimeProduct_toZModPow`: reducing the `p`-th coordinate modulo `p^k` gives Mathlib's isomorphism `Gal(F/ℚ) ≃ (ℤ/p^k)ˣ` (`IsCyclotomicExtension.Rat.galEquivZMod`) applied to the restriction of `σ` to `F`, the level of `p^k`-th roots of unity inside `ℚ(μ∞)`.
- `rationalCyclotomicCharacter`: the continuous homomorphism `Gal(ℚ(μ∞)/ℚ) → ℤ̂ˣ`, obtained by composing with the inverse of the library's isomorphism `ℤ̂ˣ ≃ ∏_p ℤ_pˣ`.

## Proof

The congruence with the finite-level character compares the actions of `σ` on a primitive `p^k`-th root of unity through the defining property of each character.

## Points to watch

The Galois group is Mathlib's automorphism group `ℚ(μ∞) ≃ₐ[ℚ] ℚ(μ∞)` with its Krull topology; no abstract model of it or of its target is used. Bijectivity of the character is proved in a separate file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Kummer/Concrete/Cyclotomic/RationalCyclotomicCharacter.lean`: the Lean file is the source byte for byte (SHA-256 `00e0252382f618058872b031d5f7f109d4182fc1fdf74d68f284d68c8027b008`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
