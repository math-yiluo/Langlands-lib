# Proof of the uniform polynomial denominator for linear recurrence series

Author: Worker 740.

## Result

`Langlands.Analysis.linearRecurrenceGeneratingSeriesStatement_proof` proves
the published closed proposition
`Langlands.Analysis.LinearRecurrenceGeneratingSeriesStatement`; its type is
exactly that declaration. The statement has no universe parameters. The
statement module and its Markdown are imported unchanged. The only other
import is `Mathlib.Analysis.SpecificLimits.Normed`, used for the real
geometric series.

No hypothesis is added. The recurrence `E : LinearRecurrence ℂ` is
arbitrary, including order zero. The solution `a` is constrained only by
Mathlib's `E.IsSolution a`. The polynomial `Q` is the statement's own
`let`-bound polynomial,
`1 - ∑ i : Fin E.order, C (E.coeffs i) * X ^ (E.order - i.val)`.

Throughout, write `d = E.order`, `c = E.coeffs` and
`S = ∑ i : Fin d, ‖c i‖`. The radius is

```text
ρ = 1 / (1 + S),
```

which depends only on `E` and is chosen before the solution `a`. The
numerator chosen for a solution `a` is

```text
A = ∑ j ∈ range d, C (a j) * X ^ j
    - ∑ i : Fin d, C (c i) * X ^ (d - i) * ∑ j ∈ range i, C (a j) * X ^ j.
```

It has degree less than `d`, although the statement does not ask for this.

## Supporting lemmas

Both lemmas are public theorems in the namespace
`Langlands.Analysis.LinearRecurrenceGeneratingSeries`.

- `norm_le_geometric E ha n`: if `E.IsSolution a`, then
  `‖a n‖ ≤ (∑ j ∈ range d, ‖a j‖) * (1 + S) ^ n` for every `n`. Write
  `C = ∑ j ∈ range d, ‖a j‖` and `R = 1 + S`, so `1 ≤ R`. The proof is by
  strong induction on `n`.
  - If `n < d`, then `‖a n‖ ≤ C` by `Finset.single_le_sum`, and
    `C ≤ C * R ^ n` because `1 ≤ R ^ n`.
  - Otherwise write `n = m + d` and rewrite with the recurrence
    `a (m + d) = ∑ i, c i * a (m + i)`. If `d = 0` this sum is empty, so its
    norm is `0 ≤ C * R ^ n`. If `d ≥ 1`, the triangle inequality
    (`norm_sum_le`) gives the bound `∑ i, ‖c i‖ * ‖a (m + i)‖`. Each `i < d`
    satisfies `m + i < m + d`, so the induction hypothesis applies:
    `‖a (m + i)‖ ≤ C * R ^ (m + i) ≤ C * R ^ (m + d - 1)`. Summing gives the
    bound `S * C * R ^ (m + d - 1)`. Then `S ≤ R` gives
    `≤ R * C * R ^ (m + d - 1) = C * R ^ (m + d)`, since `d ≥ 1`.
- `coeff_zero_reverse E`: the polynomial `Q` has constant coefficient
  one. By `coeff_sub`, `coeff_one_zero` and `finsetSum_coeff`, it suffices
  that every summand has zero constant coefficient. By `coeff_C_mul` and
  `coeff_X_pow`, the constant coefficient of `C (c i) * X ^ (d - i)` is
  `c i` times `if 0 = d - i then 1 else 0`. The condition is false because
  `i < d`, so the summand is zero. This includes `d = 0`, where the sum is
  empty.

## Main proof

Fix `E` and introduce the `let`-bound `Q`. The first conjunct is
`coeff_zero_reverse E`. Choose `ρ = 1 / (1 + S)`, which is positive because
`S ≥ 0`. Fix a solution `a`, take the polynomial `A` above, and fix `z`
with `‖z‖ < ρ`. By `lt_div_iff₀` this means `‖z‖ * (1 + S) < 1`. Since
`S ≥ 0`, this gives `‖z‖ ≤ 1`.

1. *Summability.* Let `C = ∑ j ∈ range d, ‖a j‖` and `r = (1 + S) * ‖z‖`.
   Then `0 ≤ r < 1`, so `n ↦ C * r ^ n` is summable by
   `summable_geometric_of_lt_one` and `Summable.mul_left`. By
   `norm_le_geometric`,
   `‖a n * z ^ n‖ = ‖a n‖ * ‖z‖ ^ n ≤ C * (1 + S) ^ n * ‖z‖ ^ n = C * r ^ n`.
   `Summable.of_norm_bounded` then gives
   `Summable (fun n => a n * z ^ n)` in the complete space `ℂ`.
2. *Nonvanishing of `Q`.* By `simp` with `eval_finsetSum`,
   `Q.eval z = 1 - ∑ i : Fin d, c i * z ^ (d - i)`. Suppose this is zero, so
   the sum equals `1`. Each `d - i` is nonzero and `0 ≤ ‖z‖ ≤ 1`, so
   `‖z‖ ^ (d - i) ≤ ‖z‖` by `pow_le_of_le_one`. The triangle inequality then
   gives `1 = ‖∑ i, c i * z ^ (d - i)‖ ≤ S * ‖z‖`. This contradicts
   `S * ‖z‖ ≤ (1 + S) * ‖z‖ < 1`, as `nlinarith` checks.
3. *Shift identity.* Let `F = ∑' n, a n * z ^ n`. For every `k`,
   `Summable.sum_add_tsum_nat_add` gives
   `∑' n, a (n + k) * z ^ (n + k) = F - ∑ j ∈ range k, a j * z ^ j`. The
   shifted series is summable by `summable_nat_add_iff`.
4. *Applying the recurrence.* For every `n`, the recurrence and
   `z ^ (n + d) = z ^ (n + i) * z ^ (d - i)` give
   `a (n + d) * z ^ (n + d) = ∑ i, c i * z ^ (d - i) * (a (n + i) * z ^ (n + i))`.
   Each summand is summable in `n`, by step 3 and `Summable.mul_left`. So
   `Summable.tsum_finsetSum` exchanges the finite sum with `∑'`, and
   `tsum_mul_left` pulls out the constants. Applying step 3 with `k = d` on
   the left and `k = i` on the right yields

   ```text
   F - ∑ j ∈ range d, a j * z ^ j
     = ∑ i : Fin d, c i * z ^ (d - i) * (F - ∑ j ∈ range i, a j * z ^ j).
   ```
5. *Conclusion.* By `eq_div_iff` and step 2, it suffices to prove
   `F * Q.eval z = A.eval z`. Evaluate `A` with `eval_sub`,
   `eval_finsetSum`, `eval_mul`, `eval_C`, `eval_pow` and `eval_X`, and
   distribute the identity of step 4 with `mul_sub`, `sum_sub_distrib` and
   `sum_mul`. The goal is then the identity of step 4 rearranged, closed by
   `linear_combination`.

The three facts for `z` are summability (step 1), `Q.eval z ≠ 0` (step 2)
and `∑' n, a n * z ^ n = A.eval z / Q.eval z` (step 5). They are returned
in the order of the statement.

## Provenance

The route is the "intended proof idea" recorded in the statement Markdown
`Langlands/Analysis/LinearRecurrenceGeneratingSeriesStatement.md`, written by
the same author. One detail differs: the implementation uses the ratio
`1 + S` instead of `max 1 S`, and a strong induction on `‖a n‖` instead of
the running maximum `M n`. The statement is a derived internal interface. Its
literature motivation (Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg Convolutions*, 1983, printed pp. 391–392) is recorded there
and is not used as a proof source. No external drafts or other authors'
code were reused.
