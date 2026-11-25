# Valuations of integers in a local field of mixed characteristic

Module `Nyll.ValuedFieldTheory.LocalField.Analytic.DenominatorValuation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a field `K` with a complete discrete valuation `v` with values in `ℤᵐ⁰` and finite residue field, the file packages `(K, v)` as a local field in the library's sense and, when `K` has characteristic zero, defines a ramification index `e = −log v(p)` from the valuation and computes the valuation of every positive integer: `v(m) = exp(−e · v_p(m))`, where `p` is the residue characteristic.

## Main definitions

- `coherentWithZeroMultiplicativeIntGroup`: the ordered group-with-zero structure on `ℤᵐ⁰` matching the one used by `Valuation`.
- `ofWithZeroValuation v`: `K` as a `LocalField` (the library's structure: a complete discretely valued field with finite residue field), with value group `ℤᵐ⁰` and valuation `v`.
- `ramificationIndexOfWithZeroValuation v`: the natural number `−log v(p)`, for `K` of characteristic zero.

## Main results

All assume `CharZero K`.

- `ramificationIndexOfWithZeroValuation_intCast`: `e`, as an integer, is `−log v(p)`, without truncation.
- `ramificationIndexOfWithZeroValuation_pos`: `e > 0`, because `v(p) < 1`.
- `valuation_residueCharacteristic_eq_exp_neg_ramificationIndex`: `v(p) = exp(−e)`.
- `valuation_natCast_eq_exp_neg_ramificationIndex_mul_padicValNat`: for `m ≠ 0`, `v(m) = exp(−e · v_p(m))`; writing `m = p^k a` with `p ∤ a`, the factor `a` has valuation `1`.
- `valuation_natCast_succ_eq_exp_neg_ramificationIndex_mul_padicValNat` and `valuation_natCast_factorial_eq_exp_neg_ramificationIndex_mul_padicValNat`: the same formula for `m + 1` and for `m!`, needing no nonzero hypothesis; these feed the logarithm and exponential series.

## Points to watch

- `e` is read off from the given `v` as minus the exponent of `v(p)`; the file does not compare it with a ramification index defined through degrees or ideals.
- `e` is defined as `Int.toNat`, so its definition alone would give `0` if `−log v(p)` were negative; `_intCast` and `_pos` show this does not occur.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/Analytic/DenominatorValuation.lean`: the Lean file is the source byte for byte (SHA-256 `88d50620d7ece0927bb84d872829c859a449a81b20881176ad3e50caadbd2ea9`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
