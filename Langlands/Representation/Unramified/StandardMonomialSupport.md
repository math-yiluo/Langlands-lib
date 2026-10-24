# Dominance bound for the support of the standard monomials

This module proves the support half of `StandardMonomialTriangularity` (module
`StandardMonomial`). Write `n = r + 1`, `K = GL_n(O_F)` (the spherical open subgroup),
`ϖ` for the standard uniformizer and `v` for the canonical valuation. The result is
`standardMonomial_support`: if `standardMonomial F a x ≠ 0`, then `x ∈ K ϖ^ν K` for an
antitone `ν` with `tailSum λ k ≤ tailSum ν k` for every `k` and `∑ ν = ∑ λ`, where
`λ = monomialExponent a`. So `ν` is dominated by `λ`. This is the support part of the
triangularity of products of the standard elements in Gross, *On the Satake
isomorphism* (1998), (2.8)–(2.9), retained PDF pages 4–5 (source
`gross-1998-satake-isomorphism`). The proof is ours. It compares minors, as in the
uniqueness part of the published Cartan decomposition.

## Declarations and proof

- `standardUniformizer_isUniformizing`: the unit
  `F.canonicalTopologicalData.uniformizerUnit` is an `IsUniformizingElement` for
  `ValuativeRel.valuation F.Carrier`. The published `uniformizerUnit_zpow_value` at
  exponent one says that its image under the order isomorphism
  `valueGroupWithZeroIsoInt` is `exp (-1)`. The rest copies the proof of
  `exists_isUniformizingElement`.
- `MinorDominated F lam x`: every `(n - k)`-minor of `x` has valuation at most
  `v ϖ ^ tailSum lam k`, and `v (det x) = v ϖ ^ ∑ lam`. The tuple `lam` need not be
  antitone. `tailSum_add` and `tailSum_zero` record that tail sums are additive.
- `valuation_det_of_mem_spherical`: elements of `K` have determinant of valuation
  one. The determinants of `k` and `k⁻¹` are integral (`det_mem_integer`,
  `entry_mem_of_mem`) and multiply to one.
- `minorDominated_integral_mul` and `minorDominated_mul_integral`: multiplying by an
  element of `K` on either side preserves `MinorDominated`. The minor bounds use the
  published `minor_mul_left_le` and `minor_mul_right_le`.
- `minorDominated_one`: the identity is dominated by `0`.
- `diagonal_mul_submatrix` and `minorDominated_torus_mul`: for antitone `b`,
  `MinorDominated lam x` implies `MinorDominated (b + lam) (ϖ^b x)`. A minor of
  `diag(d) · x` with rows `f` and columns `h` is `∏_s d (f s)` times the same minor of
  `x`. For injective `f`, the published `tailSum_le_sum` bounds `∑_s b (f s)` below by
  `tailSum b k`. Since `v ϖ < 1`, that gives the factor `v ϖ ^ tailSum b k`. For
  non-injective `f` two rows agree and the minor is zero. Determinant valuations
  multiply.
- `minorDominated_doubleCoset_mul`: the same bound for left multiplication by any
  `y ∈ K ϖ^b K`, writing `y = k₁ ϖ^b k₂`.
- `le_of_minorDominated_torus`: if `ϖ^ν` with antitone `ν` is dominated by `lam`, then
  `tailSum lam k ≤ tailSum ν k` and `∑ ν = ∑ lam`. The minor on the last `n - k` rows
  and columns has valuation exactly `v ϖ ^ tailSum ν k` (`sum_tailIndex`). The
  determinant gives equality of totals.
- `SupportDominated F f lam`: every `x` with `f x ≠ 0` is dominated by `lam`.
- `exists_of_mul_apply_ne_zero`: if `(f * g) x ≠ 0`, then `f y ≠ 0` and
  `g (y⁻¹ x) ≠ 0` for some `y`. Otherwise the convolution integrand vanishes.
- `standardExponent i` is `(1, …, 1, 0, …, 0)` with `i` ones. It is antitone, and
  `standardDiagonal_eq_torus` says `standardDiagonal F r i = ϖ^{standardExponent i}`.
- `supportDominated_one`, `supportDominated_standard_mul`,
  `supportDominated_pow_mul`, `supportDominated_list`: the unit is supported in `K`.
  `T_i * g` is supported in products `y z` with `y ∈ K ϖ^{standardExponent i} K` and `z`
  in the support of `g`. Induction over powers (`pow_succ'`) and over lists of
  pairs `(i, a i)` gives `supportDominated_standardMonomial`, after
  `monomialExponent_eq_sum` (`λ = ∑_i a i • standardExponent i`) and `List.sum_ofFn`.
- `standardMonomial_support`: write `x = k₁ ϖ^ν k₂` with antitone `ν` (published
  `exists_cartan`). Then `ϖ^ν = k₁⁻¹ x k₂⁻¹` is dominated by `λ`, and
  `le_of_minorDominated_torus` concludes.

Only left multiplications occur in the products. So the argument needs no
Cauchy–Binet formula, which Mathlib does not provide.
