# Prime elements and units for abstract valuations

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

With a henselian valuation `v` and its normalized valuations `v_K` on the fixed modules `A_K` of a `ℤ`-representation `A` of `G`, the file defines prime elements and the unit group, and proves how primes behave in unramified and totally ramified finite extensions.

## Main definitions and results

- `fixedFieldInclusion`: the inclusion `A_K → A_L` for `G_L ≤ G_K`.
- `relativeNorm_fixedFieldInclusion`: for a finite extension `L | K` and `a ∈ A_K`, `N(L/K)(a) = [L:K] · a`. `relativeNorm_self`: the norm of the trivial extension is the identity.
- `ValuationData.oneValue`: `1` as an element of the value group `Z`.
- `ValuationData.IsPrimeElement v K π`: `v_K(π) = 1`.
- `ValuationData.unitAddSubgroup v K`: the kernel of `v_K`, the unit group `U_K` written additively.
- `valuationAt_fixedFieldInclusion_of_unramified`: for an unramified finite extension `L | K` of fields finite over the base, `v_L(a) = v_K(a)` for `a ∈ A_K`.
- `prime_of_unramified`: a prime element of `K` stays prime in an unramified `L`.
- `norm_prime_of_totallyRamified`: in a totally ramified `L | K`, the norm of a prime element of `L` is a prime element of `K`.

The last three follow from the norm–valuation formula `f(L/K) · v_L = v_K ∘ N(L/K)`, with `N(L/K)(a) = [L:K] · a` and `f(L/K) = [L:K]` in the unramified case, `f(L/K) = 1` in the totally ramified case.

## Points to watch

- Everything is additive: a "prime element" is an element of the module `A_K` of value `1`, and the units form an additive subgroup.
- Prime elements and units are defined only for fields finite over the base (`FiniteAbstractField`).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/PrimeElements.lean`: the Lean file is the source byte for byte (SHA-256 `4f229148d57db6a5dcb056f8c27dcf4f32532c3af038dafc9675b1049434dcb7`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
