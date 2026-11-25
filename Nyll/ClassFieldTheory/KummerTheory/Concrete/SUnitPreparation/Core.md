# Rank and kernel of the S-unit preparation restriction

Module `Nyll.ClassFieldTheory.KummerTheory.Concrete.SUnitPreparation.Core`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file completes the counting in the library's S-unit preparation argument. Let `K` be a number field containing a primitive `n`-th root of unity, `E` a finite abelian extension of `K` inside a separable closure `Ω`, with an isomorphism `Gal(E/K) ≃ (ℤ/n)^r`, and `S` a finite set of finite places. After the enlargement `S' = enlargeByFiniteKummerRadicalSupport n S`, the field `E` lies in the full `S'`-unit Kummer extension `N`, whose Galois group has order `n ^ s` with `s = totalPlaceCard S'`, the number of places in `S'` plus the number of infinite places. The file compares `r` with `s` and describes the kernel `Gal(N/E)` of the restriction map.

## Main results

All statements assume `[FiniteDimensional K E] [IsGalois K E] [IsMulCommutative Gal(E/K)]`, a primitive `n`-th root of unity in `K`, and a group isomorphism `eG : Gal(E/K) ≃* (Fin r → Multiplicative (ZMod n))`.

- `galoisRank_le_totalPlaceCard_enlargedS`: for `n > 1`, `r ≤ s`.
- `card_enlargedSUnitKummerRestrictionHom_ker`: for `n > 1`, the kernel of the restriction `Gal(N/K) → Gal(E/K)` has `n ^ (s − r)` elements.
- `exists_enlargedSUnitKummerRestrictionKernelEquivPiZMod`: when `n = p ^ v` with `p` prime and `v > 0`, the kernel is isomorphic to `Fin (s − r) → Multiplicative (ZMod n)`.
- `chosenEnlargedSUnitKummerRestrictionKernelEquivPiZMod`: one such isomorphism, chosen with `Classical.choice`.

## Proofs

Restriction `Gal(N/K) → Gal(E/K)` is surjective, so `n ^ r ≤ n ^ s`, giving `r ≤ s`, and the kernel has order `n ^ s / n ^ r`. In the prime-power case, `Gal(N/K)` and `Gal(E/K)` are free `ZMod n`-modules, and the library's `exists_kernelMulEquiv_pi_zmod_of_primePower` turns the cardinality of the kernel of a surjection between them into a coordinate isomorphism.

## Remarks

- The coordinates on the kernel are stated only for prime-power `n`.
- The isomorphism `eG` is a hypothesis, not constructed here; the exponent condition on `Gal(E/K)` is derived from it.
- `s − r` is truncated subtraction of natural numbers; it is the true difference because `r ≤ s`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/KummerTheory/Concrete/SUnitPreparation/Core.lean`: the Lean file is the source byte for byte (SHA-256 `27be41b59e8c566f12907261c5988208354bf8cb4dcd0157934e5e55db40246a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
