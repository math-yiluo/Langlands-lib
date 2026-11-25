# The integer valuation attached to a `ℤᵐ⁰`-valued valuation

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.IntegerValuation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Given a valuation `v` on a field `K` with values in `ℤᵐ⁰ = WithZero (Multiplicative ℤ)`, the file builds the additive integer valuation on `Kˣ` given by `x ↦ -log v(x)`, signed so that an element of value `exp (-1)` has integer valuation `1`, and computes it on powers and on the terms `xⁿ/n` and `xⁿ/n!` of the logarithm and exponential series.

## Definitions and results

- `MultiplicativeIntegerValuation.ofWithZeroValuation v`: the integer valuation on `Kˣ`, as an element of the library's structure `MultiplicativeIntegerValuation` (a homomorphism `Kˣ → ℤ`).
- `ofWithZeroValuation_val_eq_of_valuation_eq_exp_neg`: if `v x = exp (-n)` then the integer valuation of `x` is `n`.
- `ofWithZeroValuation_val_unit_mul_pow`, `ofWithZeroValuation_val_pow`: if `v u = 1` and `v π = exp (-1)`, then `u πⁿ` and `πⁿ` have integer valuation `n`.
- `ofWithZeroValuation_val_natCast`: for `n ≠ 0` in `K` with `v n = exp (-v_p(n))`, the integer valuation of `n` is `v_p(n)` (`padicValNat p n`); the `_scaled` version allows `v n = exp (-e · v_p(n))`, for an arbitrary `e : ℕ` (meant as a ramification index).
- `ofWithZeroValuation_val_pow_div_natCast` and `..._factorial` (with `_scaled` versions): the integer valuation of `xⁿ/n` is `n · val x - v_p(n)`, and of `xⁿ/n!` is `n · val x - v_p(n!)`, or with `e ·` in front of the `p`-adic term.

## Watch for

- The `p`-adic value of the denominator is a hypothesis (`hnval`) in each statement; nothing here derives it from a characteristic or residue-characteristic assumption on `K`.
- The sign is opposite to `WithZero.log`: the integer valuation is the negative of the logarithm of `v`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/ValuationSubringUnits/IntegerValuation.lean`: the Lean file is the source byte for byte (SHA-256 `cba1c29d401e101c37edd06e94baff7fbf1731ecc2c567ad2d75f84dedab56ff`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
