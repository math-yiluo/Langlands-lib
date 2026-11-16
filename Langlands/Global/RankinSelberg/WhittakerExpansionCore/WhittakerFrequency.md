# Frequencies and sizes of algebraic integers

Module `Langlands.Global.RankinSelberg.WhittakerExpansionCore.WhittakerFrequency`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`. These are helper lemmas for half (S) of the
Whittaker expansion (see `Interface`). They supply two elementary ingredients of the decay
estimate: the real frequencies of the column characters control the size of a rational row from
below, and nonzero algebraic integers have controlled size, inverse and denominator. Here
`d = [F : ℚ]` (`Module.finrank ℚ F`) and `‖·‖` on `F` means the sup norm of
`mixedEmbedding F x` in the mixed space.

## Section `Frequency`

* `colFrequency_single`: the frequency `colFrequency F b ξ` (from `WhittakerCharDeriv`) along the
  column direction `Pi.single a u` is `Tr(b ξ_a u)`, where `Tr` is `mixedTrace` and the products
  are taken in the mixed space. Only the `a`-th summand of the defining sum survives.
* `exists_norm_le_sum_colFrequency`: for `b ≠ 0` there is `K₀ ≥ 0` such that, for every size
  `r`, every rational row `ξ ∈ F^(r+1)` and every index `a`,
  `‖ξ_a‖ ≤ K₀ Σ_k |colFrequency F b ξ (Pi.single a e_k)|`, where `e_k` runs over
  `mixedEmbedding.latticeBasis F`. Proof: the ℝ-linear map
  `z ↦ (k ↦ Tr(b z e_k))` from the mixed space to `ℝ^d` is the trace pairing composed with
  multiplication by `b`, so it is injective (`mixedTracePairing_injective`, and `b` is invertible
  in the mixed space). An injective linear map between finite-dimensional spaces is bounded
  below (`EqualAnalytic.exists_norm_le_sum_of_injective`); evaluate at `z = ξ_a` and rewrite each
  coordinate by `colFrequency_single`.
* `sum_pow_le_card_pow_mul_sum_pow`: for nonnegative reals `x_i` indexed by a nonempty finite
  type, `(Σ x_i)^K ≤ (card ι)^K Σ x_i^K`. Proof: bound the sum by `card ι` times the maximum
  term, and the `K`-th power of the maximum term by the sum of the `K`-th powers.

## Section `Integers`

* `norm_mixedEmbedding_mul_le`: `‖xy‖ ≤ ‖x‖ ‖y‖`, place by place
  (`norm_mixedEmbedding_le_iff`, `le_norm_mixedEmbedding` from `WhittakerHeights`).
* `norm_mixedEmbedding_natCast`: `‖n‖ = n` for a natural number `n`; every place gives `|n| = n`
  (`InfinitePlace.norm_embedding_eq`), and there is at least one place.
* `norm_mixedEmbedding_div_natCast`: `‖x / n‖ = ‖x‖ / n`. The case `n = 0` is trivial; otherwise
  the upper bound is place by place and the lower bound uses `x = (x / n) n` and the two
  previous lemmas.
* `one_le_norm_mixedEmbedding`: a nonzero algebraic integer `η` has `‖η‖ ≥ 1`. If all places
  were less than `1`, Mathlib's `InfinitePlace.one_le_of_lt_one` (some place is at least `1`
  for a nonzero integer) would be contradicted.
* `abs_norm_le_pow`: if `‖x‖ ≤ M` then `|N_{F/ℚ}(x)| ≤ M^d`. Proof: `|N(x)|` is the product
  of `w(x)^(mult w)` over the infinite places (`InfinitePlace.prod_eq_abs_norm`), the
  multiplicities sum to `d` (`InfinitePlace.sum_mult_eq`), and each factor is at most
  `M^(mult w)`.
* `one_le_abs_norm`: for a nonzero algebraic integer `η`, `|N_{F/ℚ}(η)| ≥ 1`, because it is a
  nonzero integer (`Algebra.coe_norm_int`, `Algebra.norm_ne_zero_iff`).
* `norm_mixedEmbedding_inv_le` (inverse bound): if `η ∈ 𝒪_F` is nonzero and `‖η‖ ≤ M`, then
  `‖η⁻¹‖ ≤ M^(d-1)`. Proof: fix a place `w`. From `1 ≤ |N(η)| = w(η)^(mult w) Π_{w' ≠ w}
  w'(η)^(mult w')` and `w'(η) ≤ M` we get `1 ≤ w(η)^(mult w) M^(d - mult w)`. Since
  `mult w ≥ 1` and `w(η) ≤ M`, this gives `1 ≤ w(η) M^(d-1)`, that is `w(η⁻¹) ≤ M^(d-1)`.
* `exists_nat_inv_integral` (denominator of an inverse): for nonzero `η ∈ 𝒪_F` with
  `‖η‖ ≤ M`, the positive integer `e = |N_{F/ℚ}(η)|` satisfies `e ≤ M^d` (by
  `abs_norm_le_pow`) and `e η⁻¹` is integral over `ℤ`. Proof of integrality: `η` divides the
  integer `N(η)` in `𝒪_F` (`Algebra.dvd_algebraMap_intNorm_self`, with `Algebra.intNorm_eq_norm`),
  say `N(η) = η c`; then `e η⁻¹ = sign(N(η)) c`, which is integral.

All statements are standard facts of algebraic number theory; their formulation (sup norm of the
mixed embedding, explicit exponents `d - 1` and `d`) is this project's own, chosen for the
lattice-sum estimates of half (S).
