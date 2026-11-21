# Comparing sorted weights in normalized bases

For a finite nonempty basis `b` over an ultrametric normed field and strictly
positive weights `w_i`, `VectorNorm.ofBasisWeights` is the norm
`a ↦ max_i |b.repr a i| w_i`. A nonzero vector has a nonzero coordinate;
scalar multiplication takes a common factor out of the maximum; and the
ultrametric inequality holds term by term. This norm is adapted to `b` and
has value `w_i` at `b i`.

`VectorNorm.sorted_weights_le_mul` compares the actual sorted weights of
`ν` and `η` in possibly different adapted bases `b` and `c`. Suppose both
bases are normalized for the same reference norm `μ`, and `ν ≤ C η`
pointwise with `C ≥ 0`. At index `i`, the span of the `c`-prefix through
`i` and the span of the `b`-suffix starting at `i` have dimensions summing
to `dim V + 1`; choose a nonzero vector `a` in their intersection. Only
prefix or suffix coordinates, respectively, can be nonzero. The adapted
basis comparisons give

```
ν(b i) μ(a) ≤ ν(a) ≤ C η(a) ≤ C η(c i) μ(a).
```

For the left bound, a maximal `b`-coefficient realizes the positive value
`μ(a)` and lies in the suffix. Divide by `μ(a)` to compare the weights.

The two finite ratio suprema for `distRatio ν η < exp ε` give pointwise
comparisons in both directions. Applying the sorted-weight comparison to
both shows that every ordered difference of the differences of sorted log
weights is less than `ε` (`log_weight_diff_lt_of_distRatio_lt`). In a
single common adapted basis the converse also holds
(`IsAdaptedBasis.distRatio_lt_exp_iff`), by the coordinate formula for the
ratio suprema.

This internal calculation uses the Library's adapted-basis norm identities
and finite-dimensional subspace dimension formula. It supplies the
coordinate comparison for aligning a star witness with a tested point, not
an identification of the vertex star with any polytope or a statement
about compact analytic domains.
