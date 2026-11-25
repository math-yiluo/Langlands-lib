# The norm index of a cyclic Kummer extension of prime-power degree

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.PrimePowerKummerIndex`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file proves that for a number field K containing the n-th roots of unity, `n = p^v` a prime power, and a Galois extension E/K with group `ℤ/n`, the idele class norm group `N_{E/K}(C_E)` has index `[E : K]` in `C_K`. It combines a counting of `C_K / C_K(S,T)` (where `C_K(S,T)` is the image of the local-power idele subgroup `h(S,T)`) with the norm containment `C_K(S,T) ⊆ N_{E/K}(C_E)`.

## Main results

- `card_sUnitPrincipalQuotient_mul_card_ideleClassQuotient_eq_power_two_totalPlaceCard`: if K has a primitive n-th root of unity, S contains every prime dividing n, and ideles supported on `S ∪ T` together with Kˣ generate `I_K`, then `#(U_{S∪T} / (U_{S∪T} ∩ h(S,T))) · #(C_K / C_K(S,T)) = n^(2s)`, with `s = totalPlaceCard S` (the number of infinite places plus `#S`).
- `card_ideleClassPowerLocalUnitQuotient_eq_finrank_sUnitKummerPrimeSet`: for E finite abelian inside a separable closure with `Gal(E/K) ≅ (ℤ/n)^r`, and the sets `S'`, `T` that the library builds from a given S (as in `principalIdelePowerLocalUnitSubgroup_eq_sUnitNthPowersInField_sUnitKummerPrimeSet`), `#(C_K / C_K(S',T)) = [E : K]`.
- `ideleClassNorm_index_eq_finrank_primePowerKummer_intermediateField`: the index statement for `Gal(E/K) ≅ ℤ/n` with E an intermediate field of a separable closure.
- `ideleClassNorm_index_eq_finrank_primePowerKummer`: the same for an arbitrary field E in `Type`.

## Proof

For the count, the principal part of `h(S',T)` is the group of n-th powers of `(S' ∪ T)`-units, whose quotient has order `n^(2s-r)` by the imported unit count, where now `s = totalPlaceCard S'`, since `#T = s - r`; the product formula then leaves `n^r = [E : K]`. For the index, S is taken to be `ideleClassHerbrandSupport`, outside of which E/K is unramified, so the norm containment applies (when n is odd and greater than 2, K has no real place); `C_K(S',T) ⊆ N(C_E)` gives that the index divides `[E : K]`, and the imported first inequality for cyclic extensions gives the reverse bound. The general E is embedded in `SeparableClosure K`, and the index is transported along the isomorphism.

## Points to watch

- The index theorem is proved only for cyclic extensions of prime-power degree n with the n-th roots of unity in K; it is not the general norm index equality.
- Apart from the first counting lemma, K and E must lie in `Type`.
- The count `#(C_K / C_K(S',T)) = [E : K]` holds for the library's particular sets `S'`, `T`, not for arbitrary ones.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/ClassFieldAxiom/IdeleClassPowerLocalUnitQuotient/PrimePowerKummerIndex.lean`: the Lean file is the source byte for byte (SHA-256 `e5fa5b28a689f0fc0b72faeb2aedf7cb1554908123607557f9b3c55de148caba`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
