# Haar measure of `GL_(t+2)` in upper-cell/lower-block coordinates

Authors: Worker 802, Worker 867.

`Langlands.RankinSelberg.RankOneExtensionCellHaarStatement.{uF}` is a closed
proposition definition. It states that the published Haar measure on
`GL_(t+2)(F)` is a positive finite multiple of the pushforward of an explicit
weighted product measure along the open-cell parametrization
`(y, m, x, a) ↦ u(y) * [m, 0; x, a]`. This module supplies no proof.

## Quantifiers and conventions

The proposition quantifies over every prime `p`, every `F : PadicField.{uF} p`,
every `t : ℕ` (including `t = 0`, where the big group is `GL_2` and `m` ranges
over `GL_1`), and every `μ : HarmonicAnalysis.AdditiveHaarMeasure F.Carrier`
(an arbitrary regular additive Haar measure, with no normalization).

It installs exactly the topology, valuative relation and local-field
certificate of `F.canonicalTopologicalData`, and the Borel σ-algebras (with
their `BorelSpace` certificates) of `F.Carrier`, of the units `F.Carrierˣ`
(units topology), of `GeneralLinear (t + 1) F.Carrier` and of
`GeneralLinear ((1 + t) + 1) F.Carrier` (Mathlib's topology on matrix units).
These are the conventions of
`Langlands.RankinSelberg.RankOneExtensionSpanComparisonStatement`. The row
space `Fin (t + 1) → F.Carrier` carries the product σ-algebra, and products of
spaces carry Mathlib's product σ-algebra.

The measures are the published ones:

- `generalLinearHaar F.Carrier (1 + t)` on `GL_((1+t)+1)` and
  `generalLinearHaar F.Carrier t` on `GL_(t+1)`: the Haar measures giving
  `GL_((1+t)+1)(O_F)`, respectively `GL_(t+1)(O_F)`, mass one;
- `rowMeasure μ (t + 1)`: the finite product of `μ.measure` on the row space
  `Fin (t + 1) → F.Carrier`, used both for the column `y` and for the row `x`;
- `localMultiplicativeHaar F.Carrier`: the Haar measure on `F.Carrierˣ` giving
  the integral units mass one.

Write `u(y)` for `rankOneExtensionUpperCell t y`, the matrix `[I, y; 0, 1]`
with the column `y` above the scalar corner, and `B(m, x, a)` for
`rankOneExtensionLowerBlock t m x a`, the matrix `[m, 0; x, a]` with
`m : GL_(t+1)`, unscaled row `x` and unit `a`. Both are the published
definitions of `RankOneExtensionAnalyticData`, in its explicit cell
coordinates of `GL_(1+(t+1))` (large block first, scalar coordinate last).
The product `u(y) * B(m, x, a)` is ascribed the type
`GeneralLinear ((1 + t) + 1) F.Carrier`, which is the same group as
`GeneralLinear (1 + (t + 1)) F.Carrier` by definitional unfolding of
`1 + (t + 1)`.

## Exact conclusion

There is `c : ℝ≥0∞` with `c ≠ 0` and `c ≠ ⊤` such that

`generalLinearHaar F.Carrier (1 + t) = c • Measure.map Φ ν`,

where `Φ (y, m, x, a) = u(y) * B(m, x, a)` (the Lean tuple is
`(y, (m, (x, a)))`), and `ν` is the right-nested product measure

`rowMeasure μ (t + 1) × (generalLinearHaar F.Carrier t × (rowMeasure μ (t + 1) × localMultiplicativeHaar F.Carrier))`

with density `(y, m, x, a) ↦ |det m|⁻¹` (`Measure.withDensity`). Here `|det m|`
is `F.canonicalTopologicalData.normalizedAbsHom (det m)`, the published
normalized absolute value (the modulus of `F`), coerced from `ℝ≥0` to `ℝ≥0∞`.

Read informally, this is the integration formula
`dg = c · dy · |det m|⁻¹ dm · dx · d^×a` on `GL_(t+2)`; the Lean proposition
asserts only the displayed equality of measures. No normalization is imposed:
`c` depends on the arbitrary `μ` and on the published Haar normalizations, and
the statement only asserts that it is nonzero and finite.

## Provenance

Derived, internal statement. JPSS, Rankin–Selberg convolutions (1983),
registered source `jpss-1983-rankin-selberg`, Lemma (5.5), printed 423–427
(PDF pages 58–62), works on `G_t = GL_t` with a lower parabolic `Q` of type
`(t₁, 1)`; in the present notation the source's `t` is `t + 2` and its `t₁` is
`t + 1`. On printed page 425 the source chooses functions supported in the open
cell `Q Ū_Q` and integrates over `Q` against its right Haar measure `d_r(q)`,
written in the coordinates `q = [1, 0; y, 1][m, 0; 0, a]`; on printed page 426
it writes
`g = [m, 0; 0, a][1, 0; x, 1][1, y; 0, 1]` and obtains the integral (8) in the
coordinates `[m, 0; x, a]`. The source never displays the Haar measure of
`GL_t` itself in cell coordinates. The present statement records that
decomposition in the order `Ū_Q · Q` with the unscaled row `x`, which is the
order needed to pass to the quotient `N_(t+2) \ GL_(t+2)` (the upper cell
`u(y)` lies in `N_(t+2)`), as required by the consumer proof of
`RankOneExtensionSpanComparisonStatement`.

The formula is the standard computation. One has
`u(y) B(m, x, a) = [m + y x, y a; x, a]` with determinant `det m · a`. The
parametrization is injective, with inverse `a = g_(t+2,t+2)`, `x` the last row
without its corner, `y = b a⁻¹` for the last column `b`, and `m = A − y x` for
the upper-left block `A`; its image is the open set where the bottom-right
entry is nonzero, whose complement is Haar-null. Haar measure on `GL_n` is
`|det g|^(-n)` times additive Haar measure on matrices; for fixed `x` and `a`
the change of variables `(y, A_m) ↦ (y a, A_m + y x)` has Jacobian `|a|^(t+1)`.
Hence, up to a positive constant,

`dg = |det m · a|^(-(t+2)) |a|^(t+1) dy dA_m dx da
    = dy · |det m|⁻¹ (|det m|^(-(t+1)) dA_m) · dx · (|a|⁻¹ da)`,

which is `dy · |det m|⁻¹ dm · dx · d^×a` with `dm` the Haar measure of
`GL_(t+1)` and `d^×a` that of `F^×`. Equivalently, `dg = dy · d_r p` with
`d_r p = |det m|⁻¹ dm dx d^×a` the right Haar measure of the lower parabolic
`p = [m, 0; x, a]`; in the source's coordinates
`p = [1, 0; y', 1][m, 0; 0, a]`, so that `x = y' m`, this is the standard
right Haar measure `dy' dm d^×a`.
