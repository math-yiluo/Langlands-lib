# Polynomial-geometric summability on finite natural-number lattices

`Langlands.FiniteNatLatticeSummabilityStatement.{uI}` is a closed proposition
bundling two summability targets. Each component quantifies over an arbitrary
`I : Type uI` with a `Fintype I` instance, a function `r : I → ℝ` with
`0 ≤ r i < 1` at every coordinate, and a real exponent `s ≥ 0`. The summand at
`k : I → ℕ` is the actual real number

```text
Real.rpow (1 + ∑ i, (k i : ℝ)) s * ∏ i, (r i) ^ (k i).
```

The height uses the sum over all coordinates. Its power is the real power
`Real.rpow`; each geometric factor has the natural exponent `k i`.
`FiniteNatLatticeRealSummabilityStatement` asserts Mathlib `Summable` for
this function on the entire tuple space `I → ℕ`.
`FiniteNatLatticeENNRealSummabilityStatement` asserts that the Mathlib `tsum`
of `ENNReal.ofReal` of exactly the same function is strictly less than `∞`.
No summation functional or dominating-series datum is supplied as a hypothesis.

There is no nonemptiness hypothesis on `I`. When `I` is empty, its tuple space
has exactly one member, the coordinate sum is zero, the coordinate product is
one, and the summand is `Real.rpow 1 s * 1 = 1`. Zero geometric ratios and
`s = 0` are included. Natural powers use the usual convention `0 ^ 0 = 1`.

## Internal provenance and proposed derivation

This is an internal elementary analysis statement, derived from finite-product
estimates and the pinned Mathlib infinite-sum APIs. It is not a translation or
quotation of an external representation-theoretic theorem. The following is a
route for a separate proof; this module only defines the propositions.

1. Choose a natural degree `d` with `s ≤ (d : ℝ)`. The height
   `H(k) = 1 + ∑ i, (k i : ℝ)` is at least one. Thus
   `Real.rpow_le_rpow_of_exponent_le`, followed by `Real.rpow_natCast`, bounds
   `Real.rpow H(k) s` by `H(k) ^ d`.
2. Finite induction on the coordinates gives
   `1 + ∑ i, (k i : ℝ) ≤ ∏ i, (1 + (k i : ℝ))`: when adding a coordinate,
   the additional cross term is nonnegative. Raising to the natural degree
   and multiplying by the nonnegative geometric product bounds the summand by
   `∏ i, ((1 + (k i : ℝ)) ^ d * (r i) ^ (k i))`.
3. For a fixed coordinate, expand `(1 + (n : ℝ)) ^ d` by the binomial theorem.
   Each resulting term is a constant multiple of
   `(n : ℝ) ^ j * (r i) ^ n`. The hypothesis `0 ≤ r i < 1` gives
   `‖r i‖ < 1`, so
   `summable_pow_mul_geometric_of_norm_lt_one` supplies summability of each
   term. Finite sums and scalar multiplication give summability of the
   one-variable bound. This argument never divides by the ratio and therefore
   includes `r i = 0`.
4. Combine the finitely many nonnegative one-variable series using
   `Summable.mul_of_nonneg`, which sums products over a product of two index
   types, and finite-type equivalences to the tuple space. The induction base
   is the singleton tuple space for an empty index type. The comparison
   theorem `Summable.of_nonneg_of_le` then gives the real clause.
5. The original summand is nonnegative. Apply
   `ENNReal.ofReal_tsum_of_nonneg` to identify the ENNReal sum with
   `ENNReal.ofReal` of its real sum, which is finite. The pinned source also
   provides the direct implication `Summable.tsum_ofReal_lt_top`. Hence the
   ENNReal clause requires no additional bridge premise.

The route was checked against Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`:

- `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` contains the real-power
  exponent comparison and natural-power identity.
- `Mathlib/Analysis/SpecificLimits/Normed.lean` contains
  `summable_pow_mul_geometric_of_norm_lt_one`.
- `Mathlib/Analysis/Normed/Ring/InfiniteSum.lean` contains
  `Summable.mul_of_nonneg` over two arbitrary index types.
- `Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean` contains the nonnegative
  comparison theorem and both real-to-ENNReal implications named above.

## Intended use and boundary

This target is an elementary summability prerequisite for later analytic
estimates for GL_n. A later adapter may identify geometric ratios from
positive simple-root gaps and actual Cartan data. This module supplies neither
that identification nor any Cartan decomposition, Haar-volume estimate,
matrix-coefficient bound, or tempered-exponent conclusion. It contains no
proof of either summability clause.
