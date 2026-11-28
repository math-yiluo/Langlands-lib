# The constants of the `(1, n)` shell identity

Module `Langlands.Representation.Shahidi.OpenCellBaseCoef`, namespace
`Langlands.Shahidi.OpenCell.Base`.

`baseConstant_eq`: for an integer `q > 0` and `D ≤ t + 1`, the product of the modulus factor
`(q^(-(t+2) D))^(1/2 + s/(t+2))`, the power `q^(α(t+1, D))` and the half modulus
`δ_B^(1/2)(ϖ^(κ(t,D)))` is `(q^(-(1+s)))^D`. Auxiliary (with the same range conditions as in
the Lean statements): `baseAlpha_two_mul` (`D ≤ t + 1`), `baseKappa_succ_apply` (`D ≤ t`),
`sum_weight_baseKappa` (`D ≤ t + 1`), `natCast_cpow_eq` (`((q^m : ℝ) : ℂ)^w = q^(m w)` for
`q > 0`), `halfModulus_eq_cpow`.

## Provenance

Elementary exponent arithmetic.
