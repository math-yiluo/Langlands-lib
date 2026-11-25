# The normalized valuation of a nonarchimedean local field

Module `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a field `K` that is a nonarchimedean local field in Mathlib's sense (`IsNonarchimedeanLocalField K`, with a `ValuativeRel` and a topology), the file defines the normalized integer valuation on `Kˣ` and proves its elementary rules. Mathlib identifies the value group with zero of `K` with `ℤᵐ⁰` (`valueGroupWithZeroIsoInt`); the normalized valuation of a unit is the exponent of its value under this identification.

## Definitions and results

- `IsNonarchimedeanLocalField.v K : Additive Kˣ → ℤ`: the normalized valuation, as a plain function on `Additive Kˣ`.
- `v_surjective`: every integer is a value; `v_uniformiser`: some unit `ϖ` has `v ϖ = 1`.
- `v_mul`, `v_one`, `v_inv`, `v_div`, `v_pow`, `v_zpow`, `v_mul_zpow`: `v` is a homomorphism, `v(xⁿ) = n · v(x)` for `n ∈ ℕ` and `n ∈ ℤ`.
- `v_zpow_of_uniformizer`, `v_mul_zpow_of_uniformizer`: if `v ϖ = 1`, then `v(ϖⁿ) = n` and `v(x ϖⁿ) = v(x) + n`.
- `v_div_eq_zero_iff`, `v_eq_iff_v_div_eq_zero`: `v(x/y) = 0` iff `v x = v y`.
- `integerUnitsToFieldUnits K : 𝒪[K]ˣ →* Kˣ`: the inclusion of the units of the valuation ring, injective, with `v = 0` on its image (`v_integerUnitsToFieldUnits`).

## Watch for

- `v` is not bundled as an additive homomorphism; its additivity is the separate lemma `v_mul`.
- The sign is that of the exponent in `ℤᵐ⁰` under Mathlib's identification; the file does not state which sign a uniformizer of the valuation ring has, only that some unit has `v = 1`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean`: the Lean file is the source byte for byte (SHA-256 `22bf0ab33bc62dffbb6e952c0aeec7a3565eb031a577e8af67e15ee54db4c496`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
