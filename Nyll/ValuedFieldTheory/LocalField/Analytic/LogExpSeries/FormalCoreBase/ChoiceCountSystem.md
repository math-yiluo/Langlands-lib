# Coordinate equations for choices of basic factors

Module `Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.ChoiceCountSystem`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In the expansion of `(X + Y + XY)^q`, a choice of one basic monomial (left `X`, right `Y`, mixed `XY`) from each factor contributes to the exponent `e = (e₀, e₁)`. This file derives the linear equations linking the numbers `L`, `R`, `M` of left, right and mixed choices to `q` and `e`.

## Main definitions and results

- `formalLogOnePlusProductArgumentBasicFactorLabelCountChoices q e`: the sequences of `formalLogOnePlusProductArgumentBasicFactorProductChoices q` whose label counts are `q - e₁` for left, `q - e₀` for right and `e₀ + e₁ - q` for mixed; `mem_formalLogOnePlusProductArgumentBasicFactorLabelCountChoices` unfolds membership.
- For one basic vector `m`: `formalLogOnePlusProductArgumentBasicFactor_left_coord` (`m(0)` is the indicator of left plus that of mixed), `…_right_coord` (likewise for `m(1)`), and `…_total_indicator` (the three indicators sum to `1`).
- Summed over the first `q` positions of a sequence with basic entries: `formalLogOnePlusProductArgument_leftCoord_sum_eq_choiceCounts` (`∑ lᵢ(0) = L + M`), `…_rightCoord_sum_eq_choiceCounts` (`∑ lᵢ(1) = R + M`) and `formalLogOnePlusProductArgument_totalChoiceCount_eq` (`L + R + M = q`).
- `formalLogOnePlusProductArgument_choiceCounts_system`: if `l` lies in `Finset.finsuppAntidiag (range q) e` and its first `q` entries are basic, then `L + M = e₀`, `R + M = e₁` and `L + R + M = q`. The first two equations are also stated separately.

The proofs compare the sums term by term using the single-vector identities.

## Points to watch

- The label-count choice set is defined with truncated subtraction in `ℕ`. It describes the intended counts only when `e₀ ≤ q`, `e₁ ≤ q` and `q ≤ e₀ + e₁`; this file neither solves the system nor relates this set to the set of choices with total exponent `e`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/Analytic/LogExpSeries/FormalCoreBase/ChoiceCountSystem.lean`: the Lean file is the source byte for byte (SHA-256 `dd26d13bfb044ac0fd8c577e6b813b4896da04ec3780b2c73aeca7109b5e1021`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
