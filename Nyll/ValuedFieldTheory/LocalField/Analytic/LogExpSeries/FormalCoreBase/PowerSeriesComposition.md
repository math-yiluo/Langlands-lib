# Formal composition of logarithm and exponential

Module `Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.PowerSeriesComposition`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file proves, in the ring of one-variable formal power series over a commutative `ℚ`-algebra, the two composition identities `exp(log(1 + X)) = 1 + X` and `log(1 + (exp X - 1)) = X`. Here `PowerSeries.log A` is Mathlib's series of `log(1 + X)` and `PowerSeries.exp A` the exponential series; `PowerSeries.subst a f` means `f` with `a` substituted for `X`.

## Main results

- `PowerSeries.alternating_mul_one_add_X`: over any commutative ring, `(∑ (-1)ⁿ Xⁿ) · (1 + X) = 1`.
- `PowerSeries.eq_zero_of_derivative_mul_one_add_X_eq_self`: over a commutative ring with `IsAddTorsionFree A`, a series `f` with constant coefficient `0` and `f' · (1 + X) = f` is `0`.
- `PowerSeries.eq_one_add_X_of_derivative_mul_one_add_X_eq_self`: under the same hypothesis, constant coefficient `1` and `f' · (1 + X) = f` force `f = 1 + X`.
- `PowerSeries.eq_X_of_derivative_eq_one`: torsion-free coefficients, `f' = 1` and constant coefficient `0` force `f = X`.
- `PowerSeries.exp_subst_log_eq_one_add_X`: for a commutative ring `A` with `Algebra ℚ A` and `IsAddTorsionFree A`, `PowerSeries.subst (PowerSeries.log A) (PowerSeries.exp A) = 1 + X`.
- `PowerSeries.log_subst_exp_sub_one_eq_X`: under the same hypotheses, `PowerSeries.subst (PowerSeries.exp A - 1) (PowerSeries.log A) = X`.

## Proofs

Both identities are proved by differentiating. The chain rule for substitution (`PowerSeries.derivative_subst`), `exp' = exp` and Mathlib's `log' · (1 + X) = 1` (`PowerSeries.derivative_log_mul_one_add_X`) show that `exp(log(1 + X))` satisfies `f' · (1 + X) = f` with constant coefficient `1`, and that `log(1 + (exp X - 1))` has derivative `1` and constant coefficient `0`. The uniqueness lemmas above finish the argument: the first is proved by induction on coefficients, the second by subtracting `1 + X`, the third by `PowerSeries.derivative.ext`; the first and third use that multiplication by a positive integer is injective.

## Points to watch

- The two composition theorems assume `IsAddTorsionFree A` in addition to `Algebra ℚ A`.
- The statements live in the namespace `PowerSeries`, beside Mathlib's own declarations.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/Analytic/LogExpSeries/FormalCoreBase/PowerSeriesComposition.lean`: the Lean file is the source byte for byte (SHA-256 `984b0dbb4c5d87cfb59f1f4363d06b637e9471a018dc4c94c7132ac2006ba292`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
