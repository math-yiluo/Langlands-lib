# Explicit lower ramification groups of finite Lubin–Tate levels

Module `Nyll.ClassFieldTheory.LubinTate.FiniteLevel.LowerRamificationFormula`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `F` be a local field structure on `K` with residue field of cardinality `q`, `π` a uniformizer, and `L_n` the standard Lubin–Tate level `n`, with `Gal(L_n/K) ≅ O_Fˣ / U_F^(n+1)`. Using the displacement formula for the primitive point `λ`, the file identifies the lower ramification groups of `L_n/K` with the images of the principal unit groups `U_F^k`.

## Main results

Throughout, `1 ≤ k ≤ n + 1` (only `k ≤ n + 1` for the first item).

- `standardLubinTateUnitParameterToGal_displacement_addVal_ge_iff_mem_parameterSubgroup`: for a parameter `a` with automorphism `σ_a`, `v(σ_a(λ) − λ) ≥ q^k` iff `a` lies in the image of `U_F^k`.
- `standardLubinTateRealLowerRamificationGroup_pow_sub_one_eq_galoisParameterSubgroup`: the lower group at `q^k − 1` is the image of `U_F^k` in `Gal(L_n/K)`; it has order `q^(n+1−k)` (`standardLubinTateRealLowerRamificationGroup_pow_sub_one_natCard`).
- `standardLubinTateUnitParameterToGal_interval_displacement_iff_mem_parameterSubgroup`: for an integer `r` with `q^(k−1) ≤ r < q^k`, `v(σ_a(λ) − λ) ≥ r + 1` iff `a` lies in the image of `U_F^k`.
- `standardLubinTateRealLowerRamificationGroup_eq_galoisParameterSubgroup_of_pow_interval` and `standardLubinTateRealLowerRamificationGroup_natCard_of_pow_interval`: for such `r`, the lower group at `r` is the image of `U_F^k`, of order `q^(n+1−k)`.

## Proof

Every automorphism comes from a parameter. Membership in a lower group at an integer index is a condition on `v(σ(λ) − λ)` (from the file on lower ramification), and the displacement results of another file translate that condition into a condition on the unit representative.

## Points to watch

- Only integer lower indices `r` with `1 ≤ r < q^(n+1)` are treated here (`r ≥ 1` since `k ≥ 1`); the lower group at `0` and at non-integer indices are handled in other files.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FiniteLevel/LowerRamificationFormula.lean`: the Lean file is the source byte for byte (SHA-256 `56a5fa779a7bb72635b98064b0154255127ff7bbff6345db6a0751cb6329f1db`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
