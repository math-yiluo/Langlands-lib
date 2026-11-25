# The order of the supported idele power quotient

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.SupportedIdeleIndex`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let K be a number field containing a primitive n-th root of unity, and S, T finite sets of finite places. The file computes the order of the quotient of `I_{S∪T}` (the ideles supported on `S ∪ T`, `IdeleGroup.supportedAt`) by its local-power subgroup `supportedIdelePowerLocalUnitSubgroup n S T` (both imported). When S contains every prime dividing n, the answer is `n^(2s)`, where `s = totalPlaceCard S` is the number of infinite places plus `#S`.

## Main results

- `card_supportedIdeleQuotient_eq_localPowerIndexProduct`: the order is the product of the archimedean factors (2 at a real place when n is even, 1 otherwise) and, over v ∈ S, of `n · n · finitePlaceNthPowerDefect n v`.
- `prod_absNorm_maxPowDividing_natCast` and `prod_finitePlaceNthPowerDefect`: if S contains every prime dividing n, the product over S of the norms of the v-parts of `(n)`, hence of the defects, is `n^[K:ℚ]`.
- `prod_infinitePlace_nthPowerIndex`: the archimedean product is `2^(r₁)` for n even and 1 for n odd.
- `prod_infinitePlace_nthPowerIndex_mul_natDegree`: the archimedean product times `n^[K:ℚ]` equals `n^(2 · #(infinite places))`.
- `card_supportedIdeleQuotient_eq_power_two_totalPlaceCard`: the order is `n^(2s)`, assuming S contains every prime dividing n.

## Proof

The quotient is split into local power quotients (imported), whose orders come from the archimedean and finite-place index formulas. The defects multiply to the norm of `(n)`, which is `n^[K:ℚ]`. The signature step uses that a field with a primitive n-th root of unity, n > 2, has no real place; the cases n = 1, 2 are checked directly.

## Points to watch

- The primitive n-th root of unity in K is assumed by `card_supportedIdeleQuotient_eq_localPowerIndexProduct`, by `prod_infinitePlace_nthPowerIndex_mul_natDegree` and by the final count, not by the other three results; the final count also needs S to contain the primes dividing n. T plays no role in the count.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/ClassFieldAxiom/IdeleClassPowerLocalUnitQuotient/SupportedIdeleIndex.lean`: the Lean file is the source byte for byte (SHA-256 `57a61e99a08e15ebb9312c9992c235728ede664182b68ebe5606794a470ce8e4`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
