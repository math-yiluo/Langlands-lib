# Standard Hecke scalars on unramified principal series

Module `Langlands.Representation.Unramified.PrincipalSeriesHecke`, namespace
`Langlands.Unramified`.

Let `I(z) = principalSeriesOfTuple F z`, the existing normalized induction from the upper
Borel subgroup (`borelShape r`) of the unramified characters `character F (z j)`. Let
`K = sphericalSubgroup F r`, let `ϖ` be the canonical uniformizer, and let
`q = residueCardinality`. The main result is `principalSeries_sum_labelledRep`. For every
`K`-fixed vector `φ` of `I(z)` and every `i : Fin (r + 2)`,

`∑ α, I(z)(labelledRep ϖ (residueLift F) α) φ = standardHeckeScalar F (ofTuple z) i • φ`,

where `standardHeckeScalar F s i = √q ^ (i (r + 1 - i)) * elementaryCoefficient s i`. Since
the left side equals the standard corner action (`StandardHeckeSum`), the standard double-coset
operators act on `I(z)^K` by these scalars. This is the classical computation in Borel
(1979), sections 7.1–7.2, and in Gross (1998), section 3. The Lean proof computes the sum
directly.

## Counting and the real scalar

- `card_radicalPairs` writes the number of radical pairs of `S` as a double sum.
- `separated_pair_count` states that the radical pairs `(a ∈ S, b ∉ S, a < b)` and the
  opposite pairs `(a ∉ S, b ∈ S, a < b)` number `|S| (m - |S|)` together. The proof swaps
  the second sum and uses that `a ∈ S`, `b ∉ S` forces exactly one of `a < b`, `b < a`.
- `radical_mul_sqrt_modulus`: for `q > 0`,
  `q ^ #RadicalPairs S * ∏_{a<b} √(q^(-e_a)) / √(q^(-e_b)) = √q ^ (|S| (m - |S|))`, where
  `e = subsetExponent S`. The proof works pair by pair: the factor of a pair is `√q` when the
  pair separates `S` and `1` otherwise.
- `elementaryCoefficient_ofTuple`:
  `elementaryCoefficient (ofTuple z) i = ∑_{S, |S| = i} ∏_{j ∈ S} z_j`. The proof expands
  `∏ (C(-z_j) X + 1)` with `Finset.prod_add` and reads off the coefficient of `X^i`.

## The principal series at the representatives

- `borelShape_eq_singletons`: `borelShape r = singletons (r + 1)` holds by `rfl`.
  `subsetLevi F ϖ S` is the diagonal Levi element `singletonLevi (ϖ^e_j)`, typed as an
  element of `(borelShape r).Levi`. `sqrtModulus F m` is the real number `√(δ_P(m))`.
- `characterRepresentation_scalar` and `blockTensor_subsetLevi`: the block tensor of the
  inducing lines (`blockCharacters F z`) acts at `subsetLevi F ϖ S` by the scalar
  `∏_j χ_j(ϖ^e_j)`. The proof uses `PiTensorProduct.ext` and `MultilinearMap.map_smul_univ`.
- `labelledRep_isUpperTriangular` and `leviProjection_labelledRep`: each representative is
  upper triangular, so it lies in the Borel subgroup (`mem_parabolic_of_isUpperTriangular`).
  Its Levi projection is `subsetLevi F ϖ S`, because its diagonal is `t_S`.
- `eval_labelledRep`: by the covariance `normalizedProductInduced_covariant`,
  `φ(x_α) = (√δ(t_S) · ∏_j χ_j(ϖ^e_j)) • φ(1)`.
- `sqrtModulus_subsetLevi`: `√δ(t_S) = ∏_{a<b} √(q^(-e_a)) / √(q^(-e_b))`. The proof uses
  `leviModulus_singletonLevi`, multiplicativity of `NNReal.sqrt`, and
  `uniformizerUnit_zpow_abs`.

## Fixed vectors and the identity

- `eval_principalSeriesOfTuple`: the action is right translation.
- `eq_zero_of_eval_one`: a `K`-fixed vector `φ` with `φ(1) = 0` is zero. Every `g` is `b k`
  with `b` in the Borel subgroup and `k ∈ K` (`exists_borel_mul_spherical`). Then
  `φ(k) = (I(k) φ)(1) = φ(1) = 0`, and by covariance `φ(b k)` is a linear image of `φ(k)`.

## The scalar

`sum_labelledRep_scalar` sums the scalar of `eval_labelledRep` over `CosetIndex`. Each subset
`S` with `|S| = i` occurs `|Λ| ^ #RadicalPairs S` times, where `|Λ| = q` is the cardinality
of the residue field. The character factor is `∏_{j ∈ S} z_j`. By
`radical_mul_sqrt_modulus` and `elementaryCoefficient_ofTuple`, the total is
`standardHeckeScalar F (ofTuple z) i`.

`principalSeries_sum_labelledRep` then works as follows. By `standardHecke_cornerAction_eq_sum`,
the sum is the corner action of `φ`, hence `K`-fixed. So the difference between the sum and
the scalar multiple of `φ` is a `K`-fixed vector. Its value at `1` is
`(∑_α c_α - c) • φ(1) = 0`, so it vanishes by `eq_zero_of_eval_one`.
