# Measure identity for the open-cell exchange

Module `Langlands.Representation.RankinSelberg.RankOneExtensionUnfoldingMeasure`.

This helper module proves the change of variables used to unfold the zeta integral of
the lower induced representation of `GL_(1+(t+1))` in the rank-one extension step. It
contains no statement about representations. It contains a matrix identity for a
rank-one shear, a measure identity for a skew map on a product space, and two facts
about product measures on `K^(t+1)`.

## Provenance

In Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg convolutions*, Amer. J. Math. 105
(1983), Lemma 5.5 (printed pp. 424–426), the integral over the lower parabolic cell is
unfolded by moving the unipotent variable `u(y)` across the lower block
`B(m, x, a) = [m, 0; x, a]`. The paper does this in one line, as a change of variables.
This module isolates that change of variables as a measure identity:

`u(y) B(1, x, h) = B(r, x, h s⁻¹) u(h s⁻¹ y)`,  with `r = I + y x`, `s = 1 + x · y`.

The block identity itself is in the companion module `RankOneExtensionCellAlgebra`.
The form of the identity, its order of factors, and the treatment of the null set
`s = 0` were chosen for this formalization; they are not quoted from the paper.

## Contents

Abstract skew product (`section Abstract`):

- `skewScalingMap φ c` is the map `((a, y), b) ↦ ((a, c(b') y), b')`, where
  `b' = φ_(a,y) b`.
- `measurable_skewScalingMap`: the skew map is measurable when `φ` and `c` are jointly
  measurable.
- `map_skewScalingMap`: suppose every `φ_(a,y)` preserves `μB`, every `c b` scales `dy`
  by a factor `w b` (`dy.map (c b) = w b • dy`), and `φ`, `c`, `w` are measurable. Then
  the skew map sends `(μA × dy) × μB` to `((μA × dy) × μB).withDensity (w ∘ snd)`. The
  measures `dy` and `μB` are assumed s-finite.

Shear (`section CellShear`), for any field `K`:

- `rankOneExtensionCellShear x y` is the element `r = I + y x` of `GL_(t+1)(K)`, where
  `y x` is the outer product `vecMulVec y x`. Its inverse is given by the
  Sherman–Morrison formula `I - s⁻¹ y x`. When `s = 1 + x · y = 0` the matrix is singular,
  and the definition returns `1` instead. The lemmas `rankOneExtensionCellShear_val` and
  `rankOneExtensionCellShear_inv_val` give the matrix and its inverse when `s ≠ 0`.
- `rankOneExtensionScalarLower a` is a unit `a` as an element of the `1 × 1`
  lower-triangular group `lowerTriangularSubgroup 1 K`. `lowerScalarEntry h` is the single
  entry of such an element; it is nonzero and multiplicative.
- `rankOneExtensionCellScalarInv x y` is `s⁻¹` in that group, and `1` when `s = 0`.

Quotient action (`section QuotientAction`):

- `continuous_rightTranslate_prod`: right translation `(q, g) ↦ q g` is jointly
  continuous on `(H \ G) × G` for a topological group `G` and any subgroup `H`.

Measurability (`section CellExchange`), for a second-countable topological field:

- `measurable_cellShear` and `measurable_cellScalarInv`: the shear and the inverse scalar
  are Borel measurable in `(x, y)`. On the open set `{s ≠ 0}` they are continuous, and
  they are constant on its complement.
- `continuous_lowerScalarEntry`.

The exchange map (`section CellExchangeMap`):

- `rankOneExtensionCellExchange H xrow` is the map on
  `(X × K^(t+1)) × ((H \ GL_(t+1)) × B⁻_1)` given by

  `((x, y), (q, h)) ↦ ((x, h' y), (q r, h'))`,  with `h' = h s⁻¹`.

  Here `x` enters only through a row `xrow x : K^(t+1)`, and `r`, `s` are computed from
  `xrow x` and `y`.
- `measurable_rankOneExtensionCellExchangeAction`, `measurable_rankOneExtensionCellScaling`
  and `measurable_rankOneExtensionCellExchange`: the fibre action, the scaling and the
  exchange map are measurable. `secondCountable_generalLinear` and
  `secondCountable_lowerTriangular` record the second countability used for this.
- `map_cellExchange`: suppose `xrow` and `w` are measurable, the measures `dy`, `μQ` and
  `ρ` are s-finite (`dx` is arbitrary), `μQ` is invariant under every right translation,
  `ρ` is right-invariant, and `y ↦ a y` scales `dy` by `w a` for every `a ≠ 0`. Then the
  exchange map sends `(dx × dy) × (μQ × ρ)` to the same measure with density
  `w(lowerScalarEntry h)`. The proof is `map_skewScalingMap`. For fixed `(x, y)`, the map
  `(q, h) ↦ (q r, h s⁻¹)` preserves `μQ × ρ`, and the scaling factor is `h' = h s⁻¹`.

Product measures (`section ProductScaling`). Here `K` is a field with a topological-ring
structure, second countable, with its Borel σ-algebra, and `ν` is a **σ-finite** measure
on `K` (`SigmaFinite ν`). Each of the three theorems below assumes the σ-finiteness of
`ν`.

- `productMeasure_map_const_smul`: let `ν` be σ-finite and `χ : K →*₀ ℝ≥0`. Suppose
  `x ↦ a x` scales `ν` by `χ(a)⁻¹` for every `a ≠ 0`. Then, for each `a ≠ 0`, `y ↦ a y`
  scales the product measure `ν^ι` over a finite type `ι` by `χ(a)^(-|ι|)`. This is the
  diagonal case of the Library's `HarmonicAnalysis.productMeasure_map_diagonal`.
- `productMeasure_cellScalar_eq_zero`: suppose `K` is also T1 and `ν` is σ-finite and has
  no atoms (`SigmaFinite ν` and `NullSingletonClass ν`). Then the hyperplane
  `{y | 1 + x · y = 0}` is `ν^(t+1)`-null for every `x`. Atomlessness alone is not enough.
  On the Borel sets of `ℝ`, let `ν` be `0` on countable sets and `∞` on uncountable
  ones. This `ν` has no atoms, but it is not σ-finite. For `t = 1` and `x = (1, 1)`, the
  finite-product construction `Measure.pi` gives the line `{1 + y₀ + y₁ = 0}` infinite
  measure, so the conclusion fails. This example is not formalized.
- `prod_cellScalar_eq_zero`: under the same assumptions on `K` and `ν`, let
  `xrow : X → K^(t+1)` be measurable and let `dx` on `X` and `μ'` on `B` be s-finite
  (`SFinite dx`, `SFinite μ'`). Then the set `{((x, y), b) | 1 + xrow(x) · y = 0}` is
  null for `(dx × ν^(t+1)) × μ'`.

## Proof method

`map_skewScalingMap` is proved by comparing measures on measurable sets, written as
lower integrals of indicator functions. It applies Tonelli (`lintegral_prod`) and the
measure preservation of `φ_(a,y)` in the fibre. It then exchanges the `y`- and
`b`-integrals (`lintegral_lintegral_swap`), uses the scaling of `dy` by `c b`, and
exchanges the integrals back.

The Sherman–Morrison identities follow from `(y x)(y x) = (x · y)(y x)`, which is
`vecMulVec_mul_vecMulVec`.

The measurability proofs use `ContinuousOn.measurable_piecewise` on the open set
`{s ≠ 0}`. Continuity into `GL_(t+1)(K)` is checked through the embedding
`Units.embedProduct`. The general linear group and the subgroup `B⁻_1` are second
countable, through the same embedding. The Borel σ-algebra on the product is therefore
the product σ-algebra, and multiplication is jointly measurable.

For the null hyperplane, choose a coordinate `j` with `x_j ≠ 0`. Split `K^(t+1)` as
`K × K^t` along `j` with `measurePreserving_piFinSuccAbove`, which needs `ν` to be
σ-finite. Each slice `{a | 1 + x · insertNth j a z = 0}` has at most one point, so it is
`ν`-null, and `Measure.prod_apply_symm` integrates the null slices. In
`prod_cellScalar_eq_zero` the set is a product with all of `B` (`Measure.prod_prod`), and
`Measure.prod_apply` integrates the `ν^(t+1)`-null fibres over `dx`. Each of these
product formulas needs only its right factor to be s-finite: `Measure.prod_prod` uses
`SFinite μ'`, and `Measure.prod_apply` uses the s-finiteness of `ν^(t+1)`, which follows
from `SigmaFinite ν`. Neither formula uses `SFinite dx`; that hypothesis is retained as
an explicit assumption in the interface of `prod_cellScalar_eq_zero`, but this proof
does not use it.
