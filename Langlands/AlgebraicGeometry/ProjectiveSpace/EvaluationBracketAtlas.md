# Powered evaluation brackets as local projective coordinates

Let `X` be a scheme and `E` a module sheaf on `X`. Let `Λ` be a type of labels,
with a module sheaf `Q r` and a morphism `ev r : E ⟶ Q r` for each label. Fix a
natural number `M`.

## Charts

A `Chart ev M` consists of the following data.

- `ρ : Fin M → Λ`: the frame labels.
- `W`: an open of `X`.
- `q r`: a section of `Q r` over `W` for every label `r`, with
  `IsFrameOn (q r) W`. That is, `q r` is a local generator: on every smaller
  open, every section is a unique function multiple of its restriction.
- `bij`: for every open `V ≤ W`, the joint evaluation
  `s ↦ (l ↦ (ev (ρ l)).app V s)` on sections of `E` over `V` is bijective.

Fix a chart `C`.

- `C.coef hV r s` is the coefficient of `(ev r).app V s` in the generator
  `q r` restricted to `V`. It is `frameCoeff`; `coefLinear`
  records that it is linear, and `coef_restrict` that it commutes with
  restriction.
- `C.e k` is the section of `E` over `W` whose joint evaluation at the frame
  labels is `q (ρ k)` in slot `k` and zero elsewhere. `C.eV hV k` is its
  restriction to `V`. `coef_frame` states that the coefficient of `C.eV hV k` at
  the label `ρ l` is `1` if `l = k` and `0` otherwise. `expand` states that every
  section over `V ≤ W` is the sum over `k` of its coefficient at `ρ k` times
  `C.eV hV k`.
- `C.mat hV σ` is the matrix with entries `coef hV (σ l) (eV hV k)` for a tuple
  of labels `σ : Fin M → Λ`. `mat_frame` gives `mat hV ρ = 1`, and `mat_restrict`
  gives compatibility with restriction.

## Coordinates

Fix `n` and trivializations `τ r : (Q r).tensorPow n ≅ 𝟙_`. The coordinate of a
tuple `σ` is

`C.coord τ σ = det (C.mat σ) ^ n * ∏ l, gauge (τ (σ l)) (q (σ l))`,

where `gauge` is the scalar gauge of `TensorPowerGauge`. `coord_restrict`
computes its restriction, and `isUnit_coord_frame` shows that the coordinate of
the frame tuple `ρ` is a unit.

## Transitions

Let `D` be a second chart. On `C.W ⊓ D.W` the following hold.

- `ratio` is the unit scaling the generators: the restriction of `D.q r` is
  `ratio r` times the restriction of `C.q r`. `ratioInv` is its inverse, and
  `ratio_mul` states that their product is `1`.
- `coef_change` and `coef_change'` compare the coefficients of the two charts
  through these ratios.
- `trans` is the change-of-frame matrix. Its column `k` holds the
  `C`-coordinates of the `k`-th frame vector of `D`.
- `mat_change` states `D.mat σ = diag(ratioInv ∘ σ) * C.mat σ * trans`.
  `det_change` takes determinants.
- `isUnit_det_trans` derives invertibility of `det trans` from `mat_frame` for
  the tuple `D.ρ`.
- `gauge_change` uses the `n`-homogeneity of gauges.
- `coord_change` combines these: the restriction of `D.coord τ σ` is
  `det (trans) ^ n` times the restriction of `C.coord τ σ`, with one unit for
  all `σ`.

`isAtlas` takes a family of charts covering `X` and an enumeration
`Fin (m + 1) ≃ (Fin M → Λ)` of the label tuples. It concludes that the
coordinates form a `CoordinateAtlas.IsAtlas`. The covering property uses the
coordinate of each chart's own frame tuple, which is a unit. The compatibility
property is `coord_change`.

## Provenance

This is an internal construction, not taken from a literature source. It
implements steps 2-4 of the intended proof recorded in the Markdown of
`TorsionBracketMapStatement`. The `n`-th powers of the maximal
minors of the joint evaluations, multiplied by gauges of trivialized `n`-th
powers of the targets, are local homogeneous coordinates whose transitions are
`n`-th powers of determinants of frame changes. They are glued with
`CoordinateAtlasGluing`. No determinant line bundle is constructed.
