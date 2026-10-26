# Polynomial-geometric summability on finite natural-number lattices

`Langlands.finiteNatLatticeSummability.{uI}` proves exactly the closed Library
proposition `Langlands.FiniteNatLatticeSummabilityStatement.{uI}`. Its two
components are also available as `finiteNatLatticeRealSummability` and
`finiteNatLatticeENNRealSummability`, in namespace `Langlands`. There are no
additional outer parameters or hypotheses.

For every `I : Type uI` with `Fintype I`, every `r : I → ℝ` satisfying
`0 ≤ r i < 1`, and every real `s ≥ 0`, the proof establishes real `Summable`
for the actual function

```text
k ↦ Real.rpow (1 + ∑ i, (k i : ℝ)) s * ∏ i, (r i) ^ (k i)
```

on the whole space `I → ℕ`. It also proves that the ENNReal `tsum` of
`ENNReal.ofReal` of this same function is strictly below `∞`.

## Implemented proof

`summable_one_add_nat_pow_mul_geometric` proves summability of
`n ↦ (1 + (n : ℝ)) ^ d * r ^ n` for a natural degree `d` and `0 ≤ r < 1`.
The proof expands `((n : ℝ) + 1) ^ d` with `add_pow`. After distributing
`r ^ n`, each term is a constant multiple of `(n : ℝ) ^ j * r ^ n`.
Nonnegativity of `r` identifies its absolute value with `r`, and
`summable_pow_mul_geometric_of_norm_lt_one` proves summability of each
term. `Summable.mul_right` and `summable_sum` then combine the finite
binomial expansion.

`summable_fintype_nat_prod` proves that a product of nonnegative, summable
coordinate functions is summable over `I → ℕ`. It uses
`Fintype.induction_empty_option`. Reindexing a finite type by an equivalence
reindexes its tuple space with `Equiv.arrowCongr`; `Equiv.summable_iff`
and `Equiv.prod_comp` preserve the claim. For the empty type, the tuple
space is finite and `hasSum_fintype` gives summability. For `Option I`,
`Equiv.piOptionEquivProd` separates the `none` coordinate from the
remaining tuple. `Summable.mul_of_nonneg` combines the two series, and
`Fintype.prod_option` identifies their product with the required finite
coordinate product.

`one_add_sum_le_prod_one_add` supplies the elementary estimate

```text
1 + ∑ i ∈ t, a i ≤ ∏ i ∈ t, (1 + a i)
```

for any finite set `t` and coordinatewise nonnegative real `a`. Induction
on `t` proves the inequality: insertion adds the nonnegative cross term
`a i * ∑ j ∈ t, a j`.

For the real target, choose a natural `d` with `s ≤ (d : ℝ)` using
`exists_nat_ge`. The height `H(k) = 1 + ∑ i, (k i : ℝ)` is at least one.
Thus `Real.rpow_le_rpow_of_exponent_le` and `Real.rpow_natCast` give
`Real.rpow H(k) s ≤ H(k) ^ d`. The finite estimate above and monotonicity
of natural powers give

```text
Real.rpow H(k) s * ∏ i, r i ^ k i
  ≤ ∏ i, ((1 + (k i : ℝ)) ^ d * r i ^ k i).
```

The first two helper results make the right side summable. The left side
is nonnegative, so `Summable.of_nonneg_of_le` proves the real target.
Finally, `Summable.tsum_ofReal_lt_top` directly gives the ENNReal target
for the same function, and the closing theorem pairs the two results.

## Provenance and boundary cases

This is an internal elementary analysis derivation of the existing Library
statement, following its proposed comparison route. No external literature
theorem or representation-theoretic assumption is used. The imported statement
and its paired Markdown are unchanged. The supporting APIs are from pinned
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`, chiefly
`Analysis/SpecificLimits/Normed.lean`,
`Analysis/Normed/Ring/InfiniteSum.lean`,
`Analysis/SpecialFunctions/Pow/Real.lean`, and
`Topology/Algebra/InfiniteSum/ENNReal.lean`.

The induction includes an empty `I`, whose tuple space is a singleton and whose
summand is one. The binomial argument never divides by `r`, so zero ratios
are included with the usual `0 ^ 0 = 1`. Degree zero and `s = 0` are included.
The proof retains the statement's real exponent and `s ≥ 0` hypothesis; it
requires no positive ratio, nonempty index type, or supplied dominating series.
Cartan coordinates, Haar-volume estimates, matrix coefficients, and their
representation-theoretic applications remain separate results.
