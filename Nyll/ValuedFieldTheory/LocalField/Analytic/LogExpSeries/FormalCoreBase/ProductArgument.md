# The two-variable series X + Y + XY

Module `Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.ProductArgument`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The logarithm product formula `log((1 + X)(1 + Y)) = log(1 + X) + log(1 + Y)` substitutes `(1 + X)(1 + Y) - 1 = X + Y + XY` into the series of `log(1 + X)`. This file defines that argument as a two-variable power series over a commutative ring and describes its coefficients.

## Main definitions and results

- `formalLogOnePlusProductArgument A : MvPowerSeries (Fin 2) A`: the series `X₀ + X₁ + X₀X₁`. `formalLogOnePlusProductArgumentPolynomial A` is the same polynomial in `MvPolynomial (Fin 2) A`; `formalLogOnePlusProductArgument_eq_coe_polynomial` identifies the two, and `formalLogOnePlusProductArgumentPolynomial_eval_pair` evaluates the polynomial at `(x, y)` to `x + y + xy`.
- `formalLogOnePlusProductArgument_eq_mul_sub_one` and `…_one_add`: the series is `(1 + X₀)(1 + X₁) - 1`.
- `formalLogOnePlusProductArgument_constantCoeff`: its constant coefficient is `0`; hence `formalLogOnePlusProductArgument_hasSubst`: it may be substituted into a one-variable power series.
- `formalLogOnePlusProductArgument_coeff`: the coefficient at `e` is the sum of the indicators of `e` being the left vector `(1, 0)`, the right vector `(0, 1)` or the mixed vector `(1, 1)`. It is `1` at each of these three (`…_coeff_single_left`, `…_coeff_single_right`, `…_coeff_mixed`) and `0` elsewhere (`…_coeff_eq_zero_of_not_basic`).
- `formalLogOnePlusProductArgument_coeff_ne_zero_eq_basic`: a nonzero coefficient occurs only at one of the three basic vectors; the coordinate bounds `e(0) ≤ 1` and `e(1) ≤ 1` are stated separately.
- `formalLogOnePlusProductArgument_pow_term_factor_eq_basic_of_prod_ne_zero`: if the product over `i < q` of the coefficients of `X + Y + XY` at `lᵢ` is nonzero, every `lᵢ` with `i < q` is basic.

Helper lemmas about `Fin 2 →₀ ℕ` show that the three basic vectors are distinct and recover a vector from its two coordinates.

## Points to watch

- The file proves only that substitution into a one-variable series is allowed; the substituted logarithm itself is not formed here.
- The polynomial version is stated over a commutative semiring, the power series over a commutative ring.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/Analytic/LogExpSeries/FormalCoreBase/ProductArgument.lean`: the Lean file is the source byte for byte (SHA-256 `ef1db20ce655bac9fe466bf88f34c588a52ba454703a0553463eb4755cf274b0`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
