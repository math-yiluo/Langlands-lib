# Strict L2 decay for one exactly extracted normalized coefficient

Author: Worker 819.

This module proves the published proposition
`Langlands.GLExtractedCoefficientL2ObstructionStatement`
(see [`ExtractedCoefficientL2ObstructionStatement`](ExtractedCoefficientL2ObstructionStatement.md))
as the theorem

`Langlands.glExtractedCoefficientL2Obstruction :
  GLExtractedCoefficientL2ObstructionStatement.{uF, uV}`.

The universes `uF` and `uV` stay independent and every quantifier of the target
is kept. The proof uses only smoothness of `ρ`, the given unitary central
character `c`, the exact deep-chamber identity, and `L²` membership of the one
coefficient. It uses no admissibility, irreducibility, exponent criterion,
Cartan volume estimate, or disjointness certificate. All helper results are
internal lemmas of this module and of
[`ExtractedCoefficientL2ObstructionCells`](ExtractedCoefficientL2ObstructionCells.md).

## Source and route

The statement Markdown records the source reading: Casselman 1995
(literature ID `casselman-1995-admissible-representations`), Proposition 1.5.2
and §4.4, Lemma 4.4.3 to Theorem 4.4.6. The statement is a derived
specialization, and so is this proof. Instead of a Haar-volume lower bound
for double cells it counts explicit disjoint unipotent translates. It also
checks strict decay only on the basic chamber tuples and the common scalars,
then concludes with the Library real-part criterion.

## Reduction to two families of tuples

`T.exists_isRealPartOf` gives a real part `x` of `χ`, since `χ` has open kernel:
`‖χ a‖ = ∏ |a_i| ^ (x_i)`. By the published
`IsRealPartOf.isPositiveRootCone_iff`, the conclusion `‖χ a‖ < 1` for monotone,
nonconstant `a` follows once `x` is in the open positive root cone: its
coordinates sum to `0` and its partial sums `x_1 + ⋯ + x_k` are positive for
`0 < k < r`. By `IsRealPartOf.sum_eq_zero_iff`, the first condition is
`‖χ (z, …, z)‖ = 1` for all `z`. For the second, let
`partialUniformizer T r k` be the tuple with the uniformizer at the indices
below `k` and `1` elsewhere. `norm_partialUniformizer` computes its character
norm as `q ^ (-(x_1 + ⋯ + x_k))`. So the second condition is
`‖χ (partialUniformizer T r k)‖ < 1`.

## Deep tuples

`exists_deep` turns the published `deepChamberNonempty` into a tuple `b₀` with
`|b₀ i / b₀ j| < ε` for all `i < j`. Multiplying by a common scalar does not
change these ratios (`deep_mul_const`). Multiplying by powers of `fₖ =
partialUniformizer T r k` multiplies each ratio by `1` or by `|ϖ| ^ M ≤ 1`
(`deep_mul_pow`). So the identity applies to `b₀ · (z, …, z)` and to every
`b₀ fₖ ^ M`, including wall directions.

## Common scalars

`norm_const_eq_one`: the block-scalar matrix of `b₀ · (z, …, z)` is that of
`b₀` times the central scalar matrix `z`. The left side of the identity
therefore picks up the unitary central character value
(`UnitaryCentralCharacter.matrixCoefficient_mul_center`). On the right side the
half modulus of a common scalar is `1` (`leviHalfModulus_const`, from
`leviModulus_scalar`), and `χ` is multiplicative. The identity at `b₀` itself
has the nonzero right side `δ^(1/2)(b₀) χ(b₀)`. Cancelling it shows that `χ (z, …, z)` equals a value
of the unitary central character, which has norm `1`.

## Basic chamber tuples

`partial_norm_lt_one`: let `0 < k < r` and suppose `‖χ fₖ‖ ≥ 1`. Put
`h₀ = blockScalar b₀` and `g = blockScalar fₖ`. Then `g` is the diagonal matrix
with `ϖ` on the set `S` of coordinates in blocks below `k` and `1` elsewhere.
`S` and `Sᶜ` are nonempty because `0 < k < r` and all block sizes are positive.

1. *Coefficient along the ray.* By the identity at `b₀ fₖ ^ M`,
   the coefficient at `h₀ g ^ M` is
   `δ^(1/2)(b₀) χ(b₀) (δ^(1/2)(fₖ) χ(fₖ)) ^ M`. Its norm is `A (h x) ^ M` with
   `A > 0`, `h = ‖δ^(1/2)(fₖ)‖` and `x = ‖χ fₖ‖`.
2. *Modulus.* `leviModulus_partialUniformizer` computes
   `δ(fₖ) = q ^ (-|S| |Sᶜ|)`, using the published
   `leviModulus_blockScalarLevi_of_abs` and `card_filter_block`.
   `norm_leviHalfModulus_sq` gives `h ^ 2 = δ(fₖ)`, hence
   `q ^ d h ^ 2 = 1` with `d = |S| |Sᶜ|`.
3. *Fixing subgroup.* `matrixCoefficient_biInvariant`, applied to the
   smooth vector `v` and the smooth-dual functional `ℓ`, gives an open subgroup
   `H` with `coef(k₁ y k₂) = coef(y)` for `k₁, k₂ ∈ H`. Let
   `KP = K ⊓ H ⊓ h₀⁻¹ H h₀`, where `K` is the integral subgroup. `K` is open by
   `maximalCompact_eq` and `isOpen_integralRange`. For `u, k ∈ KP`,
   `h₀ u g ^ M k = (h₀ u h₀⁻¹)(h₀ g ^ M) k`, so the coefficient there equals
   the coefficient at `h₀ g ^ M`. The descended norm `c.coefficientNorm`
   therefore equals `F0 M = ‖coef(h₀ g ^ M)‖` on these cells.
4. *Contradiction.* `cells_tsum_lt_top` gives `t` with
   `∑' m, q ^ (m d) F0 (m + t) ^ 2 μ(mk '' KP) < ⊤`. On the other hand,

   `q ^ (m d) (A (h x) ^ (m + t)) ^ 2 = (A (h x) ^ t) ^ 2 (q ^ d h ^ 2) ^ m (x ^ 2) ^ m ≥ (A (h x) ^ t) ^ 2 > 0`,

   since `x ≥ 1`. So every term is at least
   `ofReal ((A (h x) ^ t) ^ 2) μ(mk '' KP)`. This constant is nonzero, because
   `mk '' KP` is a nonempty open set and a Haar measure is positive on open
   sets. A series of terms bounded below by a nonzero constant is `⊤`, which
   is a contradiction. Here the squared half modulus `h ^ 2` cancels the
   factor `q ^ d` from the cell count, as in the statement's p = 2
   cancellation.

## Conclusion

`glExtractedCoefficientL2Obstruction` combines the two families into
`Exponents.IsPositiveRootCone x`. A partial sum `x_1 + ⋯ + x_k ≤ 0` would
give `‖χ fₖ‖ = q ^ (-(x_1 + ⋯ + x_k)) ≥ 1`. The theorem then applies
`IsRealPartOf.isPositiveRootCone_iff` to the given monotone, nonconstant `a`.
No separate case is needed when `B.length = 1`. There the partial-sum
conditions are vacuous, and the criterion's conclusion is vacuous too.
