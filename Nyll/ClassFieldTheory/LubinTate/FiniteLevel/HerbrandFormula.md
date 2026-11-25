# Herbrand function and upper ramification of finite Lubin–Tate levels

Module `Nyll.ClassFieldTheory.LubinTate.FiniteLevel.HerbrandFormula`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `F` be a local field structure on `K` with residue field of cardinality `q`, `π` a uniformizer, and `L_n/K` the standard Lubin–Tate level `n`, Galois of degree `(q − 1)·q^n`. From the explicit lower ramification groups of `L_n/K`, the file computes the Herbrand function `φ` at the lower breaks and identifies the upper ramification groups with the images of the principal unit groups `U_F^k`.

## Main results

- `standardLubinTateHerbrandSlope_eq_of_pow_interval`: for `1 ≤ k ≤ n + 1` and `q^(k−1) ≤ i + 1 < q^k`, the slope of `φ` on `[i, i + 1]` is `q^(n+1−k) / ((q − 1)·q^n)`, the order of the lower group divided by that of the inertia group.
- `standardLubinTateHerbrandFunction_pow_sub_one`: for `k ≤ n + 1`, `φ(q^k − 1) = k`; dually the inverse Herbrand function sends `k` to `q^k − 1` (`standardLubinTateInverseHerbrandFunction_nat_eq_pow_sub_one`).
- `standardLubinTateRealUpperRamificationGroup_nat_eq_lower_pow_sub_one`: for `k ≤ n + 1`, the upper group at `k` equals the lower group at `q^k − 1`.
- `standardLubinTateRealUpperRamificationGroup_nat_eq_galoisParameterSubgroup` and `standardLubinTateRealUpperRamificationGroup_natCard`: for `1 ≤ k ≤ n + 1`, the upper group at `k` is the image of `U_F^k` in `Gal(L_n/K)` and has order `q^(n+1−k)`.
- `standardLubinTateRealUpperRamificationGroup_eq_natCeil`, `standardLubinTateRealUpperRamificationGroup_eq_galoisParameterSubgroup_of_ceil`, `standardLubinTateRealUpperRamificationGroup_natCard_of_ceil`: for real `t` with `1 ≤ ⌈t⌉ ≤ n + 1`, the upper group at `t` equals the one at `⌈t⌉`, hence is the image of `U_F^⌈t⌉`, of order `q^(n+1−⌈t⌉)`.
- `standardLubinTateRealLowerRamificationGroup_eq_break_of_pow_interval`: the lower group at an integer `r` with `q^(k−1) ≤ r < q^k` equals the one at `q^k − 1`.

## Proof

The lower group at `0` is the whole Galois group, so the slopes come from the lower group orders computed in an earlier file. By induction on `k`, the `(q − 1)·q^k` slopes on `[q^k − 1, q^(k+1) − 1]` sum to `1`, which gives `φ(q^k − 1) = k`. Upper groups are lower groups at the inverse Herbrand function; for real `t`, strict monotonicity of the inverse Herbrand function places it between consecutive breaks.

## Points to watch

- All statements are confined to the range visible at level `n`: integer indices `k ≤ n + 1` (with `k ≥ 1` for the unit-group descriptions), and real `t` with `0 < t ≤ n + 1`. The upper groups beyond `n + 1`, and at `t < 0`, are not described here.
- The upper and lower groups are the library's real-indexed filtrations, defined through the unique extension of the valuation to `L_n`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FiniteLevel/HerbrandFormula.lean`: the Lean file is the source byte for byte (SHA-256 `8352824b191e74e8ad4f0e24b652f0300adcbaf0fd288d2b837d3ad63b1837b7`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
