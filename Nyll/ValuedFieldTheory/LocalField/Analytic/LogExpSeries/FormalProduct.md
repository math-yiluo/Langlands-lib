# The formal logarithm product formula

Module `Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalProduct`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file proves `log((1 + X)(1 + Y)) = log(1 + X) + log(1 + Y)` in `A⟦X, Y⟧` for every commutative `ℚ`-algebra `A`, with Mathlib's `PowerSeries.log A`, and prepares its evaluation at points of a topological ring.

## Main definitions

- `formalLogOnePlusLeftVariableLogSubst A`, `formalLogOnePlusRightVariableLogSubst A`: `log(1 + X)` and `log(1 + Y)` as two-variable series; `formalLogOnePlusProductRightSide A` is their sum.
- `formalLogOnePlusProductFormulaDefect A`: the difference between `log` substituted at `X + Y + XY` and the right side.
- `mvPowerSeriesMonomialValue a d`: the value `∏ₛ a(s)^(d(s))` of the monomial with exponent `d`.

## Main results

- `formalLogOnePlusProductFormula`: `PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A) = formalLogOnePlusProductRightSide A`.
- `formalLogOnePlusProductArgument_pow_coeff_eq_card_choices`: the coefficient at `e` of `(X + Y + XY)^q` is the number, cast into `A`, of length-`q` basic-factor choices with total exponent `e`; it vanishes when `e(0) + e(1) < q` (also stated with the total degree of `e`), when `q < e(0)` and when `q < e(1)`.
- `formalLogOnePlusProduct_alternating_sum_choose_eq_zero`: for `a, b > 0`, the sum over `m ≤ a` of `(-1)^m C(a, m) C(a + b - 1 - m, a - 1)` vanishes in `ℚ`; `formalLogOnePlusProduct_rational_mixed_sum_eq_zero` is the resulting vanishing of the mixed logarithmic sum.
- `formalLogOnePlusProductFormula_aeval`: the identity survives `MvPowerSeries.aeval` at any point with `MvPowerSeries.HasEval`, when `A` is complete, Hausdorff, a uniform additive group, a topological ring and linearly topologized. `mvPowerSeries_hasEval_fin_two` gives such points from two topologically nilpotent elements.
- `hasSum_formalLogOnePlusProductArgument_pow_monomialValue_pair`: the monomial expansion of `(X + Y + XY)^q` at `(x, y)` is finitely supported with sum `(x + y + xy)^q`.
- `formalLogOnePlusProductFormula_hasSum_monomialValue_eq`: in a commutative `ℚ`-algebra with a Hausdorff topology, if the monomial expansions of both sides at a point have sums `L` and `R`, then `L = R`.

## Proof

The formula is checked coefficient by coefficient. On the axes, `(X + Y + XY)^d ≡ X^d` modulo `Y` (and symmetrically), so on both sides the coefficient of `Xⁿ` is the `n`-th coefficient of `log`. At `e = (a, b)` with `a, b > 0` the right side vanishes, and the coefficient of the substituted logarithm is a finite sum over `q` between `max(a, b)` and `a + b` of `(-1)^(q-1)/q` times the choice count. Reindexing by `q = a + b - m` and multiplying by `a` turns it, up to sign, into the alternating binomial sum, which is the coefficient of `X^(a-1)` in `X^a (X + 1)^(b-1)`, hence zero.

## Points to watch

- `formalLogOnePlusProductFormula_hasSum_monomialValue_eq` takes the convergence of both monomial expansions as hypotheses; it proves no convergence.
- Here `log` always means the series of `log(1 + X)`.
- The `aeval` version needs a linear topology on `A`; the `HasSum` version only Hausdorffness.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/Analytic/LogExpSeries/FormalProduct.lean`: the Lean file is the source byte for byte (SHA-256 `5864949084aae0ca03041f4630a4b79d4b34ed9d96ca402dc2ccb93d1e309d2c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
