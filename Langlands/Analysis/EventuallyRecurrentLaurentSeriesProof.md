# Proof of uniform Laurent rationality for eventually recurrent sequences

Author: Worker 740.

## Result

`Langlands.Analysis.eventuallyRecurrentLaurentSeriesStatement_proof` proves
the published closed proposition
`Langlands.Analysis.EventuallyRecurrentLaurentSeriesStatement`; its type is
exactly that declaration. The statement has no universe parameters. The
statement module and its Markdown are imported unchanged. The other imports
are the published modules
`Langlands.Analysis.LinearRecurrenceGeneratingSeriesProof`, for the natural
generating-series theorem, and
`Langlands.Representation.RankinSelberg.LaurentEvaluation`, for regularity
and evaluation of images of Laurent polynomials.

No hypothesis is added. The recurrence `E`, the weight `m > 0`, the sequence
`c` and the cutoffs `L`, `N` are arbitrary, as in the statement. The
hypothesis `L ≤ (N : ℤ)` is accepted but not needed by the proof. The
polynomials `Q` and `D` are the statement's own `let`-bound objects.

## Witnesses

Fix `E` and its polynomial `Q`. The theorem
`linearRecurrenceGeneratingSeriesStatement_proof E` gives `Q.coeff 0 = 1`, a
radius `ρ > 0`, and for every natural solution `a` a polynomial `A` with the
generating-series properties. The same `ρ` is used here, so it still depends
only on `E`.

Fix `m > 0` and write `Qm = Q.comp (X ^ m)`, so `D = Qm.toLaurent`. For data
`c`, `L`, `N` satisfying the hypotheses, apply the natural theorem to the tail
`a j = c (j + N)` to get `A`, and set

```text
H = ∑ n ∈ Ico L N, C (c n) * T (m * n)      (a Laurent polynomial),
B = X ^ (m * N) * A.comp (X ^ m)            (a polynomial),
R = laurentToRatFunc H + B / Qm             (in RatFunc ℂ),
P = H * Qm.toLaurent + B.toLaurent.
```

Here `B / Qm` means the quotient of the `algebraMap` images of `B` and `Qm`
in `RatFunc ℂ`. These witnesses depend on `E`, `m`, `c`, `L` and `N`, but not
on the evaluation point.

## Supporting lemmas

The splitting theorem is in the namespace
`Langlands.Analysis.EventuallyRecurrentLaurentSeries`; the rational-function
evaluation lemma is reused from `Langlands.RankinSelberg`.

- `summable_and_tsum_split f L N hf htail`: if `f : ℤ → ℂ` vanishes below `L`
  and `j ↦ f (j + N)` is summable over `ℕ`, then `f` is summable and
  `∑' n, f n = ∑ n ∈ Ico L N, f n + ∑' j : ℕ, f (j + N)`. The proof writes
  `f = g + h`, with `g n = f n` for `n < N` and `h n = f n` for `n ≥ N`, both
  zero otherwise. `g` vanishes outside `Ico L N`, so it is summable with sum
  `∑ n ∈ Ico L N, f n` (`summable_of_ne_finset_zero`, `tsum_eq_sum`). The map
  `e j = j + N` from `ℕ` to `ℤ` is injective, `h` vanishes off its range and
  `h ∘ e = (j ↦ f (j + N))`. Therefore `Function.Injective.summable_iff` and
  `Function.Injective.tsum_eq` transfer the summability and the sum of the
  tail. `Summable.tsum_add` finishes the proof.
- `regular_and_eval_div z B D hD`: if `D.eval z ≠ 0`, the rational function
  `B / D` has reduced denominator nonzero at `z` and evaluates to
  `B.eval z / D.eval z`. The reduced denominator divides `D`
  (`RatFunc.denom_div_dvd`), which gives regularity. Evaluating
  `(B / D) * D = B` with `RatFunc.eval_mul` and `RatFunc.eval_algebraMap` gives
  the value. The theorem
  `Langlands.RankinSelberg.regular_and_eval_div` in
  `Langlands.Representation.RankinSelberg.LaurentEvaluation`, by Workers 233
  and 759, is public and reused directly. Its abbreviation
  `RationalFunctions` is definitionally `RatFunc ℂ`.

## Main proof

1. *Constant coefficient and radius.* `Q.coeff 0 = 1` and the radius come
   directly from the natural theorem.
2. *`D ≠ 0`.* The constant coefficient of `Qm` is `Qm.eval 0 = Q.eval (0 ^ m)`.
   Since `m > 0`, this is `Q.eval 0 = Q.coeff 0 = 1`, using
   `coeff_zero_eq_eval_zero`, `eval_comp` and `zero_pow`. So `Qm ≠ 0`, and
   `Polynomial.toLaurent_eq_zero` gives `D ≠ 0`.
3. *Clearing.* `laurentToRatFunc` is a ring homomorphism with
   `laurentToRatFunc_toLaurent`. So the image of `P` is
   `laurentToRatFunc H * Qm + B`, and the image of `D` is `Qm`, in
   `RatFunc ℂ`. Since `Qm` is nonzero there (`RatFunc.algebraMap_ne_zero`),
   `Qm * (laurentToRatFunc H + B / Qm) = laurentToRatFunc H * Qm + B` by
   `mul_add`, `mul_div_assoc'` and `mul_div_cancel_left₀`; `ring` closes the
   commutation.
4. *Summability.* Fix `z ≠ 0` with `‖z ^ m‖ < ρ` and put `w = z ^ m ≠ 0`. The
   natural theorem gives summability of `j ↦ c (j + N) * w ^ j`,
   `Q.eval w ≠ 0` and
   `∑' j, c (j + N) * w ^ j = A.eval w / Q.eval w`. By `zpow_add₀`, each tail
   term satisfies `c (j + N) * w ^ (j + N) = w ^ N * (c (j + N) * w ^ j)`, so
   the tail of `n ↦ c n * w ^ n` is summable (`Summable.mul_left`). The
   sequence vanishes below `L` because `c` does. `summable_and_tsum_split`
   then gives summability of the bilateral series and the decomposition
   `∑' n, c n * w ^ n = ∑ n ∈ Ico L N, c n * w ^ n + w ^ N * (A.eval w / Q.eval w)`,
   using `tsum_mul_left`.
5. *Regularity.* Let `x = Units.mk0 z hz`. The theorem
   `laurentToRatFunc_regular_and_eval x H` shows that `laurentToRatFunc H`
   has reduced denominator nonzero at `z`, with value `laurentEval x H`.
   Since `Qm.eval z = Q.eval w ≠ 0`, `regular_and_eval_div` shows that
   `B / Qm` has reduced denominator nonzero at `z`, with value
   `B.eval z / Qm.eval z`. By `RatFunc.denom_add_dvd`, the reduced denominator
   of `R` divides the product of the two denominators. That product is
   nonzero at `z`, so `R.denom.eval z ≠ 0`.
6. *Value.* `RatFunc.eval_add`, valid because both summands are regular at
   `z`, gives `RatFunc.eval z R = laurentEval x H + B.eval z / Qm.eval z`.
   By `map_sum`, `laurentEval_C`, `laurentEval_T` and `zpow_mul`, the first
   term is `∑ n ∈ Ico L N, c n * w ^ n`. The second is
   `w ^ N * A.eval w / Q.eval w`, because `B.eval z = w ^ N * A.eval w` by
   `eval_comp` and `pow_mul`. This matches the decomposition of step 4.

The three facts for `z` are returned in the order of the statement:
summability (step 4), regularity (step 5) and the value (step 6).

## Provenance

The route follows the proof sketch in the statement Markdown
`Langlands/Analysis/EventuallyRecurrentLaurentSeriesStatement.md`: split off
the finite head, apply the natural-series theorem to the tail at `w = z ^ m`,
and represent the tail by `X ^ (m * N) * A(X ^ m) / Q(X ^ m)`. One detail
differs. That sketch clears the negative exponents of `H` into a single
polynomial quotient. The implementation instead keeps `R` as the sum of
`laurentToRatFunc H` and a polynomial quotient. It obtains regularity from
the published `laurentToRatFunc_regular_and_eval` and the divisibility
`RatFunc.denom_add_dvd`. The statement is a derived internal interface. Its
literature motivation (Jacquet, Piatetski-Shapiro and Shalika,
*Rankin-Selberg Convolutions*, 1983, printed pp. 391–392) is recorded there
and is not used as a proof source. The proof reuses
`Langlands.RankinSelberg.regular_and_eval_div` from the Library module
described above, preserving Workers 233 and 759's proof unchanged.
