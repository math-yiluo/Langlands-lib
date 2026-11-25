# Counting basic-factor choices in (X + Y + XY)^q

Module `Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCore`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The coefficient of `X^a Y^b` in `(X + Y + XY)^q` counts the ways of picking a left (`X`), right (`Y`) or mixed (`XY`) monomial from each of the `q` factors with total exponent `(a, b)`. This file computes that number as a product of two binomial coefficients, by identifying a choice with the pair formed by its set of mixed positions and its set of left positions. It completes the combinatorial core built in the `FormalCoreBase` files.

## Main definitions and results

- `formalLogOnePlusProductArgumentMixedLeftChoices q a b`: the pairs `(M, L)` with `M ⊆ range q` of size `a + b - q` and `L ⊆ range q \ M` of size `q - b`. `formalLogOnePlusProductArgumentMixedLeftChoices_card`: there are `C(q, a + b - q) · C(q - (a + b - q), q - b)` of them.
- `formalLogOnePlusProductArgumentBasicFactorLabelCountChoices_card_eq_mixedLeftChoices_card`: under `e(0) ≤ q`, `e(1) ≤ q` and `q ≤ e(0) + e(1)`, the label-count choices for `e` are in bijection with the pairs above for `a = e(0)`, `b = e(1)`. The bijection sends a choice to its mixed and left positions and a pair to `formalLogOnePlusProductArgumentChoiceFromMixedLeft`; the four lemmas `…_toMixedLeft_mem`, `…_fromMixedLeft_mem`, `…_from_to_choice`, `…_to_from_pair` check it.
- `formalLogOnePlusProductArgumentBasicFactorLabelCountChoices_subset_choices`: under the same bounds, every label-count choice is a genuine choice with total exponent `e`.
- `formalLogOnePlusProductArgumentBasicFactorChoices_card_eq_choose_mul_choose`: under the same bounds, the number of choices with total exponent `e` is `C(q, e(0) + e(1) - q) · C(q - (e(0) + e(1) - q), q - e(1))`, that is, the multinomial number of ways to place `e(0) + e(1) - q` mixed, `q - e(1)` left and `q - e(0)` right factors.
- `formalLogOnePlusProductArgument_choiceCounts_left_coord_le_q` and `…_right_coord_le_q`: a sequence with basic entries and total exponent `e` forces `e(0) ≤ q` and `e(1) ≤ q`.

## Proofs

The cardinality of the pair set is a sum over `M` of `card (powersetCard …)`. The choice set equals the label-count set by the inclusion proved in the explicit-count file and the reverse inclusion here, which recomputes the coordinate sums from the label counts; the bijection with pairs then gives the count.

## Points to watch

- The counting formula is stated only under `e(0) ≤ q`, `e(1) ≤ q`, `q ≤ e(0) + e(1)`; all subtractions are truncated in `ℕ`.
- The count is a natural number. Its use as a power-series coefficient, and the vanishing outside the bounds, are not in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/Analytic/LogExpSeries/FormalCore.lean`: the Lean file is the source byte for byte (SHA-256 `e71202f81dbfa2140d57890c7180883237fc896f47f5158641faf9fcdeff5e35`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
