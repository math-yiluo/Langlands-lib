# Conductors of finite abelian local extensions

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Conductor`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite abelian extension `L / K` of a nonarchimedean local field `K`, this file defines the conductor exponent as the least `n ≥ 0` such that the principal-unit group `U_K^(n)` lies in the norm subgroup `N(L^×)`, and the conductor as the ideal `𝔭_K ^ n` of the valuation ring of `K`.

## Main definitions and results

- `fieldPrincipalUnits_antitone`: `U_K^(n) ≤ U_K^(m)` when `m ≤ n`.
- `exists_fieldPrincipalUnits_le_normSubgroup`: for `L / K` finite and abelian Galois (`[IsAbelianGalois K L]`) over a nonarchimedean local field, some `U_K^(n)` lies in `localNormSubgroup K L`. The proof combines openness of the norm subgroup (`localNormSubgroup_isOpen`) with the fact that the principal-unit groups form a neighbourhood basis of `1`.
- `localConductorExponent`: the least such `n`, defined by `Nat.find`. `localConductorExponent_spec` and `localConductorExponent_min` give its defining property and minimality; `localConductorExponent_le_iff` says `f ≤ n` exactly when `U_K^(n)` consists of norms.
- `localConductorIdeal`: the ideal `𝓂[K] ^ localConductorExponent K L` of `𝒪[K]`.
- `localConductorExponent_eq_zero_iff`, `localConductorIdeal_eq_one_iff_exponent_eq_zero`, `localConductorIdeal_eq_one_iff`: the conductor is the unit ideal exactly when the exponent is zero, exactly when the full unit group `U_K = U_K^(0)` consists of norms.

## Points to watch

The conductor is defined through the norm subgroup, not through ramification groups or Artin characters; the file proves no comparison with those. The exponent counts from `U_K^(0) = U_K`, the full unit group. The existence of the least exponent is proved, not assumed.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Conductor.lean`: the Lean file is the source byte for byte (SHA-256 `536ddd3cf1d199d1b0b87cb8b10d91c91bd79872d8e813e83be173c1adb90ed4`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
