# The n-th power quotient of the S-unit group

Module `Nyll.ClassFieldTheory.KummerTheory.Concrete.SUnitPreparation.SUnitPowerQuotient`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be a number field and `S` a finite set of finite places. This file computes `Kˢ / (Kˢ)ⁿ` for the `S`-unit group `Kˢ`: it is finite, and when `K` contains a primitive `n`-th root of unity it has order `n ^ s` with `s = #(infinite places) + #S`, with explicit `ZMod n` coordinates. It then identifies `Kˢ / (Kˢ)ⁿ` with `(Kˢ · Kˣⁿ) / Kˣⁿ`, the radical quotient that defines the full `S`-unit Kummer extension.

## Main definitions and results

- `totalPlaceCard S`: `#InfinitePlace K + #S`. `totalPlaceCard_eq_sUnitLogRank_add_one`: it equals the free rank `SUnitGroup.logRank S` of `Kˢ` plus one.
- `finite_sUnit_nthPowerQuotient` (instance): `Kˢ / (Kˢ)ⁿ` is finite, for `n > 0`.
- `card_sUnit_nthPowerQuotient`: if `K` has a primitive `n`-th root of unity, `|Kˢ / (Kˢ)ⁿ| = n ^ totalPlaceCard S`.
- `sUnitNthPowerQuotientCoordinates`: under the same hypothesis, `Kˢ / (Kˢ)ⁿ ≃* ℤ/n × (ℤ/n)^{logRank S}` (written multiplicatively).
- `n_dvd_numberField_torsionOrder`, `card_numberField_torsion_nthPowerQuotient`, `numberFieldTorsionNthPowerQuotientEquivZMod`: with a primitive `n`-th root of unity, `n` divides the number of roots of unity of `K`, and their quotient by `n`-th powers is cyclic of order `n`.
- Helpers on `ℤ^d / nℤ^d ≅ (ℤ/n)^d` (`finsuppModHom`, `finsuppNsmulQuotientEquivPiZMod`, `card_finsupp_nsmulQuotient`) and `multiplicativeZModProductEquivPiSucc`, which merges one coordinate with `r` others into `r + 1`.
- `mem_sUnitGroup_of_pow_mem`: if `xⁿ` is an `S`-unit, so is `x`.
- `fullSUnitKummerSubgroup n S`: the Kummer subgroup `Kˢ · Kˣⁿ` of `Kˣ`.
- `sUnitNthPowerQuotientEquivFullSUnitRadicalQuotient`: the canonical map `Kˢ / (Kˢ)ⁿ → (Kˢ · Kˣⁿ) / Kˣⁿ` is an isomorphism. Hence `finite_fullSUnitRadicalQuotient` and `card_fullSUnitRadicalQuotient`: this quotient is finite, of order `n ^ totalPlaceCard S` under the root-of-unity hypothesis.

## Proofs

The count uses the library's decomposition `SUnitGroup.decomposition`, an isomorphism of `Kˢ` with the roots of unity times `ℤ^{logRank S}`, from another file. The quotient of a product by `n`-th powers splits; the torsion factor, cyclic of order divisible by `n`, contributes `n`; the free factor contributes `n ^ logRank`. Injectivity of the comparison map rests on `mem_sUnitGroup_of_pow_mem`, proved from valuations; surjectivity holds because every element of `Kˢ · Kˣⁿ` is an `S`-unit times an `n`-th power.

## Remarks

- The coordinate isomorphisms pass through the chosen decomposition and an isomorphism of cyclic groups of equal order; they are not canonical.
- Only the counts and coordinates need the primitive `n`-th root of unity; finiteness and the comparison isomorphism hold for every positive `n`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/KummerTheory/Concrete/SUnitPreparation/SUnitPowerQuotient.lean`: the Lean file is the source byte for byte (SHA-256 `dd9036d4956a524e190b9e660e32079f02a93f0beda30ab72c2fd7c0ef7aae58`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
