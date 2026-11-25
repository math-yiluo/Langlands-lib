# Solving the count equations for basic-factor choices

Module `Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.ExplicitChoiceCounts`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `l` pick one basic monomial (left `X`, right `Y` or mixed `XY`) from each of the `q` factors of `(X + Y + XY)^q`, with total exponent `e = (e₀, e₁)`, and let `L`, `R`, `M` be the numbers of left, right and mixed picks. The previous file gives `L + M = e₀`, `R + M = e₁`, `L + R + M = q`; this file solves the system.

## Main results

The results about a single `l` assume that `l` lies in `Finset.finsuppAntidiag (range q) e` and that its first `q` entries are basic; the inclusion and the comparison of cardinalities hold for all `q` and `e`.

- `formalLogOnePlusProductArgument_choiceCounts_total_add_mixed_eq_coord_sum`: `q + M = e₀ + e₁`; hence `…_q_le_coord_sum`: `q ≤ e₀ + e₁`.
- `formalLogOnePlusProductArgument_choiceCounts_explicit`: `L = q - e₁`, `R = q - e₀`, `M = e₀ + e₁ - q`, also stated one at a time.
- `formalLogOnePlusProductArgument_labelCounts_explicit`: the same values for the label counts `0`, `1`, `2`; `formalLogOnePlusProductArgumentBasicFactorChoices_labelCounts_explicit` states it for members of `formalLogOnePlusProductArgumentBasicFactorChoices q e`.
- `formalLogOnePlusProductArgumentBasicFactorChoices_subset_labelCountChoices`: every choice with total exponent `e` lies in `formalLogOnePlusProductArgumentBasicFactorLabelCountChoices q e`; hence `…_card_le_labelCountChoices` compares cardinalities.

The proofs are rearrangements in `ℕ` followed by cancellation of the added term.

## Points to watch

- Subtraction is truncated in `ℕ`. The bounds `e₀ ≤ q` and `e₁ ≤ q`, implicit in these identities, are not stated in this file.
- Only one inclusion between the choice set and the label-count set is proved here; the reverse inclusion, which needs the bounds on `e`, is not in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/Analytic/LogExpSeries/FormalCoreBase/ExplicitChoiceCounts.lean`: the Lean file is the source byte for byte (SHA-256 `bcf85cd2eabf427abc3685a0d96837270e9e8700299e1aa928be4f705d9b63ea`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
