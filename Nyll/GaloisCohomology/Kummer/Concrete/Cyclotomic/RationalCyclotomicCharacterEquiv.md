# Gal(ℚ(μ∞)/ℚ) is isomorphic to ℤ̂ˣ

Module `Nyll.GaloisCohomology.Kummer.Concrete.Cyclotomic.RationalCyclotomicCharacterEquiv`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file proves that the cyclotomic character `Gal(ℚ(μ∞)/ℚ) → ℤ̂ˣ` is bijective and upgrades it to an isomorphism of topological groups. Here `ℚ(μ∞)` is the library's `rationalCyclotomicField` inside a separable closure of `ℚ`, its finite levels are `rationalCyclotomicLevel n = ℚ(ζ_n)`, and the character is the product of Mathlib's `p`-adic cyclotomic characters.

## Main results

- `rationalCyclotomicCharacterPrimeProduct_toZModPow_of_dvd`: for `p^k ∣ n`, the reduction modulo `p^k` of the `p`-th coordinate of the character of `σ` is the image, under `(ℤ/n)ˣ → (ℤ/p^k)ˣ`, of the class in `(ℤ/n)ˣ` given by Mathlib's `IsCyclotomicExtension.Rat.galEquivZMod` for the restriction of `σ` to `ℚ(ζ_n)`.
- `rationalCyclotomicCharacterPrimeProduct_injective` and `rationalCyclotomicCharacter_injective`: the character into `∏_p ℤ_pˣ`, and hence into `ℤ̂ˣ`, is injective.
- `rationalCyclotomicCharacter_surjective`: the character is surjective onto `ℤ̂ˣ`.
- `rationalCyclotomicCharacterContinuousMulEquiv`: the resulting isomorphism of topological groups `Gal(ℚ(μ∞)/ℚ) ≃ₜ* ℤ̂ˣ`.
- `zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter` (simp): its `p`-th component in `∏_p ℤ_pˣ` is the `p`-adic cyclotomic character.

## Proofs

Injectivity: if two automorphisms have the same character, the Chinese remainder theorem (`ZMod.equivPi`) and the congruence above show that they agree on every level `ℚ(ζ_n)`; since the levels exhaust `ℚ(μ∞)`, they are equal. Surjectivity: for `u ∈ ℤ̂ˣ`, the sets of `σ` whose restriction to `ℚ(ζ_n)` matches `u mod n` are closed, and any finitely many of them meet (lift from the level indexed by the product of the indices); compactness of the Galois group gives a common point, whose character is `u`, checked modulo every `p^k`. The topological isomorphism follows from the compact-to-Hausdorff criterion.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Kummer/Concrete/Cyclotomic/RationalCyclotomicCharacterEquiv.lean`: the Lean file is the source byte for byte (SHA-256 `65753650359f2c929e3436bdad748399b052a0d6b48ed564b206bf22cb790812`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
