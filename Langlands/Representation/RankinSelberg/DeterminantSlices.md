# Determinant slices and equal-rank slice coefficients

## Source

Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg convolutions* (1983),
Section 4.2, (4.2.1), printed page 406 (registered source
`jpss-1983-rankin-selberg`). For an integer `m` the source sets

`G_r^m = {g ∈ G_r : |det g| = q^(-m)}`

and defines

`Ψ^m(W, W'; Φ) = ∫_{N_r \ G_r^m} W(g) W'(g) Φ(η_r g) dg`.

Here `η_r = (0, ..., 0, 1)`, so `Φ(η_r g)` is `Φ` evaluated at the last row of
`g`. The source attaches these coefficients to the equal-rank integral (2.4.1).
On printed page 407 it deduces, from convergence of (2.4.1) for `Re s` large
and Fubini's theorem, that each `Ψ^m` converges and that (4.2.2)
`Ψ(s) = Σ_m q^(-ms) Ψ^m`. Neither the convergence nor (4.2.2) is formalized
here; no convergence, support bound, compactness, or Laurent expansion of the
full integral is asserted.

The source definitions are `determinantSlice` (the quotient `N \ G^m`) and
`equalRankSliceCoefficient` (the coefficient `Ψ^m`). Everything else in the
module is derived API: the quotient order, its topology and right-translation
laws, the general restricted coefficient `sliceCoefficient`, its
integrability predicates and linearity, and the pointwise spectral weight.

## Setting

Everything is stated for arbitrary `p : ℕ` with `[Fact p.Prime]`, a p-adic field
`F : PadicField.{uF} p` (field universe kept), and topological data
`T : F.TopologicalData`. It therefore specializes to
`F.canonicalTopologicalData`. The rank is the positive actual rank `n + 1`. The
quotient is the Library's actual left quotient
`LeftUnipotentQuotient n F.Carrier = N_(n+1) \ GL_(n+1)` by the upper unipotent
subgroup, carrying the quotient topology induced by `T.topology`. Topological
statements are written with `letI := T.topology` inside the statement, as in the
Library's `generalLinearDeterminant`. The right-translation statements also
install `T.valuativeRel` and `T.localField`, which the quotient right
translation needs.

## Quotient determinant order and slices

- `determinantOrder T n : LeftUnipotentQuotient n F.Carrier → ℤ` descends
  `g ↦ T.ord (det g)` along the quotient with `QuotientIntegration.descend`.
  Independence of the representative is `det (u g) = det g` for upper unipotent
  `u` (`determinant_unipotent_mul`, from `unipotent_det`).
  `determinantOrder_mk` evaluates it on a representative (definitionally).
- `determinantSlice T n m = {q | determinantOrder T n q = m}`, for every
  integer `m`. `mem_determinantSlice` and `mk_mem_determinantSlice` unfold
  membership. `mk_mem_determinantSlice_iff_normalizedAbs` proves the source
  condition: `[g] ∈ S_m` iff `T.normalizedAbs (det g) = q^(-m)`, with
  `q = T.residueCardinality`. The proof uses `T.normalizedAbs_of_ne_zero`, which
  applies because the determinant of an invertible matrix is nonzero, and the
  injectivity of `m ↦ q^m` for `q > 1`.
- `continuous_ord_units`: `a ↦ T.ord a` is continuous from the field units
  into the discrete integers. Each fiber is a coset of the kernel of
  `T.ordUnits`. That kernel equals the open kernel of the normalized absolute
  value on units (`T.ker_ordUnits`, `T.isOpen_ker_normalizedAbsUnits`).
- `continuous_determinantOrder`: the quotient order is continuous into `ℤ`
  with its discrete topology. It is the lift of the composite of
  `continuous_ord_units` with the continuous determinant
  `T.generalLinearDeterminant (n + 1)`.
- `isClopen_determinantSlice`, `isOpen_determinantSlice`,
  `isClosed_determinantSlice`: slices are open and closed.
  `measurableSet_determinantSlice`: each slice is measurable for every Borel
  measurable structure on the quotient (supplied as
  `[MeasurableSpace _] [BorelSpace _]` binders). In particular this covers the
  structure `borel _` used for the coefficients below.
- `disjoint_determinantSlice`, `pairwise_disjoint_determinantSlice`: distinct
  slices are disjoint. `iUnion_determinantSlice`: their union is the whole
  quotient.

The slices are determinant fibers; nothing is claimed about compactness, and
in general they are not compact.

## Right translation

`determinantOrder_rightTranslate`: for actual `g` and `q`,

`d(QuotientIntegration.rightTranslate _ g q) = d(q) + T.ord (det g)`.

The proof uses multiplicativity of the determinant and `T.ord_mul`.
`rightTranslate_mem_determinantSlice` is the matching membership formula:
`q·g ∈ S_m` iff `q ∈ S_(m - ord(det g))`. No measure invariance is involved.

## Restricted coefficients

The measurable structure on the quotient is fixed: it is
`borel (LeftUnipotentQuotient n F.Carrier)`, the Borel structure of the
quotient topology induced by `T.topology`. As in the Library's statement
modules, the measure argument has type
`letI := T.topology; letI := borel _; Measure (LeftUnipotentQuotient n F.Carrier)`,
and the definitions and statements install the same `borel` structure with
`letI`. So the supplied measure `μ` is always a measure on the quotient's
Borel sets; no other measurable structure can be used. For an arbitrary
function `f : LeftUnipotentQuotient n F.Carrier → ℂ`:

- `sliceCoefficient T μ f : ℤ → ℂ`, with
  `sliceCoefficient T μ f m = ∫ q in S_m, f q ∂μ` (`sliceCoefficient_def`). The
  output is an ordinary function `ℤ → ℂ`; no series type is introduced.
- `SliceIntegrableAt T μ f m` means `IntegrableOn f S_m μ` for the Borel
  structure (`sliceIntegrableAt_iff`), and
  `SliceIntegrable T μ f := ∀ m, SliceIntegrableAt T μ f m`. Both are
  `Prop`-valued.
- Closure: `SliceIntegrableAt.add`, `SliceIntegrableAt.smul`,
  `SliceIntegrable.add`, `SliceIntegrable.smul` (complex scalars).
  `sliceIntegrable_of_integrable` derives slice integrability from a global
  `Integrable f μ`. Global integrability is not assumed elsewhere.
- Linearity: `sliceCoefficient_add` (under slice integrability of both
  summands at `m`) and `sliceCoefficient_add_fun` (at every `m`).
  `sliceCoefficient_smul` and `sliceCoefficient_smul_fun` hold without any
  integrability hypothesis, since Bochner integrals commute with scalar
  multiplication unconditionally.
- `sliceCoefficient_eq_integral_indicator`: the coefficient is the full
  integral of the indicator of the slice. The proof uses that the slice is
  Borel measurable (`measurableSet_determinantSlice`).

## Equal-rank coefficients (JPSS (4.2.1))

Let `abv = normalizedAbsoluteValue T`. For a unitary additive character `ψ`,
`W : WhittakerFunctions ψ n`, `W' : InverseWhittakerFunctions ψ n`, and a
Schwartz–Bruhat row function `Φ`:

- `equalRankSliceCoefficient T μ ψ W W' Φ : ℤ → ℂ` is `sliceCoefficient` of
  the existing `equalRankIntegrand ψ abv W W' Φ 0`, so
  `equalRankSliceCoefficient T μ ψ W W' Φ m = ∫ q in S_m,
  equalRankIntegrand ψ abv W W' Φ 0 q ∂μ` (`equalRankSliceCoefficient_def`).
  This is `Ψ^m(W, W'; Φ)` of (4.2.1) with the supplied measure `μ` in place
  of the source quotient measure `dg`. The measure `μ` has the same type as in
  the previous section, so it is a measure on the quotient's Borel sets.
- `equalRankIntegrand_zero_mk` (stated for any topological field and any
  absolute value): on a representative, the integrand at `s = 0` is exactly
  `W(g) * W'(g) * Φ(lastRow g)`, the source integrand. The determinant weight
  at zero is `x^0 = 1` (`determinantWeight_zero`).
- `equalRankIntegrand_eq_mul_spectralPoint_zpow`: for every `s : ℂ` and every
  `q ∈ S_m`, the integrand at `s` equals its value at zero times
  `(spectralPoint T.residueCardinality s) ^ m`. Here `m` is an integer
  exponent and `spectralPoint q s = q^(-s)`. The proof reuses
  `normalizedDeterminantWeight_eq_spectralPoint_zpow`. No summation is
  involved.
- `setIntegral_equalRankIntegrand_determinantSlice`:
  `∫ q in S_m, equalRankIntegrand ψ abv W W' Φ s q ∂μ =
  equalRankSliceCoefficient T μ ψ W W' Φ m * spectralPoint q s ^ m`. Since the
  integrands agree on the measurable slice and a constant factor commutes with
  the Bochner integral, this identity needs no integrability hypothesis.
- `sliceIntegrableAt_equalRankIntegrand_iff`: slice integrability at `s` is
  equivalent to slice integrability at zero, because the factor
  `spectralPoint q s ^ m` is nonzero.

No irreducibility, Whittaker type, smoothness, or Haar normalization premise is
used.
