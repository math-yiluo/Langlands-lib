# Decay of cusp forms with unbounded determinant

Provenance: internal. This module is a supporting lemma module for the proof of
`Langlands.Global.RankinSelbergGlobal.UnequalAnalyticStatement` (Cogdell 2004, Theorem 2.1).
Cogdell attributes the convergence of the unequal-rank global integral to the rapid decay of
cusp forms. The Library's decay results (`Langlands.Automorphic.CuspidalL2`) cover adelic
matrices whose determinant lies in a fixed band. The global integral has no such
restriction, so this module proves three estimates that let the determinant be unbounded. Each
estimate is first proved for an arbitrary real function `w` on `GL_n(𝔸)` with the needed
bounds, and then specialized to `w = ‖f‖` for a cuspidal vector `f`. The general versions keep
the cusp-form evaluation out of the long proofs, which makes them faster to elaborate.

Notation: `torInf F n x` is the archimedean torus element with entries `exp (x i)`,
`A(x) := AdelicGL.ofInfinite F n (torInf F n x)`, `mean x := (∑ j, x j) / n`,
`d := [F : ℚ]`, `absDet F n g` is the idelic norm of `det g`, and `Chamber K x`, `Q₁`,
`exists_siegelDecomposition`, `chamber_alternative`, `floor_chamber`, `shift_chamber`,
`leftTranslateCover` are from `Langlands.Automorphic.CuspidalL2.{SiegelCover, CompactCover}`.
All declarations are in the namespace `Langlands.Global.RankinSelbergGlobal.UnequalAnalytic`.

## Means of real vectors

- `sum_sub_mean x`: `∑ (x i - mean x) = 0`.
- `sum_abs_le_sum_abs_sub_mean x`: `∑ |x i| ≤ ∑ |x i - mean x| + |∑ x|`, by the triangle
  inequality in each coordinate.
- `abs_sum_le_of_coordinate_bounds x hk hk'`: if `-C ≤ x k` and `x k' ≤ C`, then
  `|∑ x| ≤ n (∑ |x i - mean x| + C)`. Proof: `|x k - mean x|` and `|x k' - mean x|` are at
  most the `ℓ¹` distance `D` to the mean, so `-(D + C) ≤ mean x ≤ D + C`. Then use
  `∑ x = n mean x`.

## Chamber decay with unbounded sum

- `HasChamberDecay w Q K` (definition): there is `A ≥ 0` such that for every `c ≥ 0` there is
  `C` with `w (A(x) q) ≤ C exp (-c ∑ |x i - mean x|) exp (A |∑ x|)` for all `x` in
  `Chamber K` and `q ∈ Q`. The rate `A` does not depend on `c`.
- `hasChamberDecay_of_bounds w hK hgrowth hdecay`: if `w` satisfies the polynomial growth
  bound `w (A(x) q) ≤ C H(x)^d` (the shape of `OperatorRealization.exists_torus_growth`,
  `H` the archimedean matrix height) and the rapid decay across every maximal block (the
  shape of `OperatorRealization.exists_blockDecay`), then `HasChamberDecay w Q K` holds with
  `A = c₀ (d₁ + d₂)`. Here `H(x) ≤ C₀ exp (c₀ ∑ |x i|)`
  (`exists_matrixHeight_torInf_le`). Proof: put `x' = x - mean x`, which lies in the same
  chamber and has sum `0`. Apply `chamber_alternative` to `x'` with `R = 0`.
  - If `∑ |x' i| ≤ B₀`, then the growth bound and `∑ |x i| ≤ ∑ |x' i| + |∑ x|` give the
    estimate, with `exp (c B₀)` absorbing `exp (-c ∑ |x' i|)`.
  - Otherwise some block gap of `x` is at most `-ℓ`, and `∑ |x' i| ≤ B₀ + n³ ℓ`. Block decay
    with `N = ⌈n³ (c + d₂ c₀)⌉` and the real inequality `decay_exponent_le` give the
    estimate.

  The constant is the sum of the constants of the two cases.

## Decay from a basis column and a basis row

- `log_absDet_torInf_mul x q`: `log |det (A(x) q)| = d ∑ x + log |det q|`.
- `exists_abs_log_absDet_le hQ`: `|log |det||` is bounded on a compact set.
- `le_of_basis_column_row_of_hasChamberDecay w hw hdecay hn N hN`: let `w` be left
  invariant under `GL_n(F)` with chamber decay on every compact set and chamber. Then for
  every `N ≥ 0` there is `C` with `w g ≤ C exp (-N |log |det g||)` whenever some column and
  some row of `g` are standard basis vectors. Proof: write `γ g = A(x) q` by the Siegel
  decomposition (`q ∈ Q₁`, `x ∈ Chamber K`). By `exists_coordinate_bounds` (module
  `UnequalAnalyticHeights`) some `x k ≥ -C'` and some `x k' ≤ C'`. So
  `|∑ x| ≤ n (D + C')` with `D = ∑ |x i - mean x|`, and
  `|log |det g|| ≤ d |∑ x| + L`, where `L` bounds `|log |det||` on `Q₁`. Chamber decay with
  `c = (A + N d) n` gives
  `w g ≤ C exp (-(A + N d) n D + A |∑ x|)`, and the exponent is at most
  `(A + N d) n C' + N L - N |log |det g||`.

## A weighted lattice cover

- `summable_lattice_bound P A`: `m ↦ A exp (-∑ |m i|)` is summable over any subtype of
  `ℤ^n` (`summable_prod_fin`, `summable_exp_neg_mul_abs_int`).
- `exists_weighted_cover_of_hasChamberDecay` (for a Borel measurable structure on
  `GL_n(𝔸)`): there is one measurable set `t` meeting the rational orbit of every adelic
  matrix with the following property. For every `w` with chamber decay on every compact set
  and chamber, there is `B₀` such that
  `∫⁻_t ofReal (w x) · ofReal (exp (-B |log |det x||)) dμ < ∞` for every `B ≥ B₀` and every
  left-invariant measure `μ` that is finite on compact sets. Construction:
  `t = ⋃_m A(m) Q₂`, the left translates of the compact set `Q₂ = A([0,1]^n) Q₁` by the
  integer chamber vectors `m ∈ Chamber (K + 1)`. It meets every orbit because of the Siegel
  decomposition and `x = ⌊x⌋ + fract x` (`floor_chamber`). Proof of finiteness: take `A` and
  `C` from chamber decay on `Q₁` and `Chamber (K + 2)` with `c = 1`, and put `B₀ = A + 1`.
  For `z = A(y) q ∈ Q₂` the vector `X = m + y` lies in `Chamber (K + 2)` and satisfies
  `∑ |m i| - n ≤ ∑ |X i|` (`shift_chamber`). Chamber decay, the inequality
  `|log |det (A(X) q)|| ≥ |∑ X| - L` and `∑ |X i| ≤ ∑ |X i - mean X| + |∑ X|` then bound the
  integrand on `A(m) Q₂` by `|C| exp (B L + n) exp (-∑ |m i|)`, since `B ≥ A + 1`. These
  bounds are summable over `m`, and `lintegral_leftTranslateCover_lt_top` concludes.

## Cusp forms

For an `OperatorRealization F n` `S` (with compact adelic quotient `𝔸/F`):

- `hasChamberDecay S hS f Q hQ hK`: for a cuspidal `S` and `f : S.Space`, the function
  `g ↦ ‖f(g)‖` has chamber decay on every compact `Q` and every chamber `K ≥ 0`. This is
  `hasChamberDecay_of_bounds` applied to `S.exists_torus_growth` and
  `S.exists_blockDecay`.
- `exists_norm_le_of_basis_column_row S hS f hn N hN`: for every `N ≥ 0` there is `C` with
  `‖f(g)‖ ≤ C exp (-N |log |det g||)` whenever some column and some row of `g` are standard
  basis vectors. Uses `le_of_basis_column_row_of_hasChamberDecay`, where left invariance is
  `evaluate_rational`.
- `exists_weighted_cover S hS`: one measurable set `t` meeting every rational orbit such
  that, for every `f : S.Space`, `∫⁻_t ‖f(x)‖ₑ exp (-B |log |det x||) dμ < ∞` for all large
  `B` and all such `μ`. Uses `exists_weighted_cover_of_hasChamberDecay`.
