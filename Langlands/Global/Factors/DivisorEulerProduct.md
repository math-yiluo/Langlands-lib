# Divisor Euler products with finite exceptional factors

Worker 1692 derives this internal analytic support from Mathlib's absolute
convergence of finite-subset product expansions and dominated convergence for
series. The index type is arbitrary, in universe `u`. A divisor is an
integer-valued finitely supported function `d : ι →₀ ℤ`. This module does not
assert a number-field or class-group interpretation of these divisors.

For a finite set `S` and complex weights `h i k`, `coefficient S h d` is the
product of `h i (d i)` over `S ∪ d.support`. In particular, every exceptional
zeroth coefficient remains present, including when it vanishes. No division by
such coefficients is used. The associated `coefficientGraph` records `(i, d i)`
at all these indices, and `mem_coefficientGraph` describes its membership.
`coefficientGraph_injective` recovers a divisor from its augmented graph.

The weight `graphWeight S h (i, k)` equals `h i k` if `i ∈ S` or `k ≠ 0`, and
zero otherwise. `prod_graphWeight` recovers the coefficient as a product of
these weights along its graph. Assume that the real family indexed by `ι × ℤ`
which is `‖h i k‖` for `k ≠ 0` and zero for `k = 0` is summable. The norm of
`graphWeight` is then summable: the additional zero-index terms lie in the
finite set `S × {0}`. Mathlib's
`summable_finsetProd_of_summable_nonneg`, restricted along the injective graph,
proves `summable_norm_coefficient`, absolute summability of the divisor series.
This conclusion does not require the zeroth coefficients outside `S` to be one.

`finite_series_product` states the finite-dimensional product-of-series law:
for a finite type `α`, if every `h i` is absolutely summable over `ℤ`, then the
series over all tuples `d : α → ℤ` with summand `∏ i, h i (d i)` is absolutely
summable and its sum is `∏ i, ∑' k, h i k`. The implemented proof inducts on
finite types, using the empty type and `Option α`. The option case is reindexed
as one integer coordinate times the remaining tuple; absolute summability and
Mathlib's `tsum_mul_tsum_of_summable_norm` give the induction step. Equivalence
invariance handles arbitrary finite types.

For a finite set `T`, `supportEquiv T` restricts divisors supported in `T` to
integer tuples on `T`, using Mathlib's `Finsupp.restrictSupportEquiv` and
`Finsupp.equivFunOnFinite`. Now also assume `h i 0 = 1` whenever `i ∉ S`.
If `S ⊆ T`, `coefficient_eq_prod` extends the defining finite product to all of
`T`, since each additional factor is one. `sum_restrict_support` reindexes the
sum over supported divisors using this equivalence and applies the finite
product-of-series law.

Finally, `hasProd_tsum` proves the unconditional, unordered identity

```
HasProd (fun i => ∑' k, h i k)
  (∑' d : ι →₀ ℤ, coefficient S h d).
```

Its assumptions are exactly the joint norm summability away from `k = 0` and
the condition `h i 0 = 1` outside the finite set `S`. Joint summability gives
absolute summability of every local series by adjoining its one zero-index
term. The restricted summand is the coefficient when `d.support ⊆ T` and zero
otherwise. It converges pointwise to the coefficient as `T` tends to infinity
through finite sets, and its norm is bounded by the absolutely summable
coefficient norm. Mathlib's `tendsto_tsum_of_dominated_convergence` therefore
identifies the limit of the restricted sums. Once `T` contains `S`, those sums
are exactly the finite local products, proving the displayed `HasProd`.

This is general series support for the global Hecke proof. It does not prove
that actual local Mellin weights satisfy its norm hypothesis, identify the
series with an adelic integral, or prove the global functional equation.

Integration uses module-specific names for local instances. Their types, values,
and local instance scopes are unchanged.
