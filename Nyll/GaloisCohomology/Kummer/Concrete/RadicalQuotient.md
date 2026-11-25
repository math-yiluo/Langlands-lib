# The ambient radical quotient and its Kummer character

Module `Nyll.GaloisCohomology.Kummer.Concrete.RadicalQuotient`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a field extension `L/K` and a radical datum `D` (a subgroup `Δ ≤ Kˣ` with a chosen `n`-th root in `Lˣ` of each of its elements), the file builds the Kummer character `Δ → Hom(Gal(L/K), μ_n(L))`, `a ↦ (σ ↦ σ(α)/α)` with `α` the chosen root of `a`, and shows that its kernel is `Δ ∩ Kˣⁿ` when `L/K` is Galois. The roots are chosen arbitrarily, not multiplicatively; a hypothesis that Galois fixes `μ_n(L)` makes the characters independent of the choice.

## Main definitions

- `kummerCharacterWithoutSection hfixed`: the homomorphism `Δ → Hom(Gal(L/K), μ_n(L))`, built from `rootCharacterToMuWithoutSection`.
- `ambientNthPowersSubgroup`: the elements of `Δ` that are `n`-th powers in `Kˣ`, that is `Δ ∩ Kˣⁿ`.
- `RadicalQuotient`: the quotient `Δ/(Δ ∩ Kˣⁿ)`, with its projection `radicalQuotientMk`, its lift `radicalQuotientLift`, and an induction principle.
- `quotientKummerCharacterWithoutSection`: the Kummer character descended to this quotient.

## Main results

- `rootCharacter_mul_withoutSection`, `rootCharacter_one_withoutSection`: the root characters are multiplicative in `a` although the choice of roots is not.
- `ambientNthPowersSubgroup_le_ker`: ambient `n`-th powers have trivial character.
- `ker_kummerCharacterWithoutSection_eq_ambientNthPowers`: if `L/K` is Galois, the kernel is exactly `Δ ∩ Kˣⁿ`.
- `quotientKummerCharacterWithoutSection_injective`: hence the descended character is injective.

## Proofs

Multiplicativity compares the chosen root of `ab` with the product of the chosen roots, which have the same `n`-th power. For the kernel, an element with trivial character has its chosen root fixed by every automorphism, so the root lies in `K` by the Galois correspondence (`InfiniteGalois.mem_range_algebraMap_iff_fixed`), and `a` is an `n`-th power in `Kˣ`.

## Points to watch

- `hfixed` (every `σ` fixes every `u ∈ Lˣ` with `u^n = 1`) is a hypothesis of the root characters, the Kummer character, its descent and the results about them, but not of `ambientNthPowersSubgroup`, `RadicalQuotient`, its projection or its lift; it says that `Gal(L/K)` fixes `μ_n(L)` pointwise, as happens when `μ_n(L)` lies in the image of `K`.
- The denominator is `Δ ∩ Kˣⁿ`, which may be larger than the subgroup of `n`-th powers of elements of `Δ`.
- The Galois hypothesis is only needed for the kernel and injectivity, and `L/K` need not be finite.
- Surjectivity of the character is not proved here.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Kummer/Concrete/RadicalQuotient.lean`: the Lean file is the source byte for byte (SHA-256 `914b1908aa2c1581eecca54f38551226822a690cc99177070d84412ffc4bd384`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
