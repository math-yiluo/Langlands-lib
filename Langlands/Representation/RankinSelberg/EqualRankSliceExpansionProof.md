# Proof of the conditional equal-rank determinant-series expansion

Author: Worker 762.

The module
`Langlands.Representation.RankinSelberg.EqualRankSliceExpansionProof`
proves the published proposition
`Langlands.RankinSelberg.EqualRankSliceExpansionStatement.{uF}` as the theorem

`Langlands.RankinSelberg.equalRankSliceExpansion {p : ℕ} [Fact p.Prime]
(F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
EqualRankSliceExpansionStatement F T n`.

Every parameter of the target is retained: the field universe `uF`, every
prime `p`, every `F`, every supplied `T : F.TopologicalData`, and every
`n : ℕ`, including actual rank one (`n = 0`). Inside the proposition, the
proof keeps the supplied topology `T.topology`, the exact Borel structure
`borel (LeftUnipotentQuotient n F.Carrier)`, and every measure `μ` on it,
every `ψ : UnitaryAdditiveCharacter F.Carrier`, every standard and inverse
Whittaker function `W`, `W'`, every row Schwartz–Bruhat function `Φ`, and
every `s : ℂ`. The only premise used is the target's
`EqualRankConverges ψ (normalizedAbsoluteValue T) μ W W' Φ s`, which by
definition is Bochner integrability of the equal-rank integrand at `s`
with respect to `μ`.

## Original source

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, Section 4.2, formulas (4.2.1)–(4.2.2). The registered original is
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed page 406 (zero-based PDF index 40) defines
`G_r^m = {g : |det g| = q^(-m)}` and the coefficient (4.2.1)
`Ψ^m(W, W'; Φ) = ∫_(N_r \ G_r^m) W(g) W'(g) Φ(η_r g) dg`. Printed page 407
(zero-based PDF index 41) states that, because (2.4.1) converges for large
`Re(s)`, Fubini makes each coefficient convergent and gives (4.2.2),
`Ψ(s, W, W'; Φ) = Σ_(m ∈ ℤ) q^(-ms) Ψ^m(W, W'; Φ)`. Worker 762 read both
pages visually in the retained scan. No registered erratum specific to this
source was found in the project literature index or the current Library
notes.

The source deduces these facts from its separately proved convergent
half-plane. The present theorem proves only the conditional partition
step: at one parameter `s` that is assumed convergent, it derives the three
conclusions below. It does not prove the half-plane convergence.

## Implemented proof

The proof has two reusable partition lemmas and the main theorem. Both
lemmas work for any measure `μ` on the Borel structure of the actual
quotient and any function into a real Banach space `E`. They use no Haar
property, invariance, sigma-finiteness or local finiteness of `μ`.

### `hasSum_setIntegral_determinantSlice`

If `f` is integrable for `μ`, then
`HasSum (fun m : ℤ => ∫ q in determinantSlice T n m, f q ∂μ) (∫ q, f q ∂μ)`.

The published `DeterminantSlices` module supplies
`measurableSet_determinantSlice` (each slice is open, hence Borel),
`pairwise_disjoint_determinantSlice`, and `iUnion_determinantSlice`
(the slices cover the quotient). The proof applies Mathlib's
`MeasureTheory.hasSum_integral_iUnion` to this countable, measurable,
pairwise disjoint family indexed by `ℤ`. Its integrability premise on the
union is the restriction of global integrability. Finally it rewrites the
union as `Set.univ` and uses `Measure.restrict_univ`.

### `summable_norm_setIntegral_determinantSlice`

If `f` is integrable for `μ`, then the norms
`‖∫ q in determinantSlice T n m, f q ∂μ‖` are summable over `m : ℤ`.
The previous lemma, applied to the integrable real function `‖f‖`, shows
that `m ↦ ∫ q in determinantSlice T n m, ‖f q‖ ∂μ` is summable. Each norm
of a slice integral is nonnegative and at most this slice integral of the
norm, by `norm_integral_le_integral_norm`. Comparison
(`Summable.of_nonneg_of_le`) then gives summability.

### `equalRankSliceExpansion`

Let `f` be `equalRankIntegrand ψ (normalizedAbsoluteValue T) W W' Φ s`,
which is integrable by the premise. Write
`a(m) = equalRankSliceCoefficient T μ ψ W W' Φ m` and
`z = spectralPoint T.residueCardinality s`.

1. Slice integrability at zero. The published
   `sliceIntegrable_of_integrable` gives integrability of `f` on every
   determinant slice. For each `m`, the published
   `sliceIntegrableAt_equalRankIntegrand_iff` transfers it to the integrand
   at parameter zero. That equivalence holds on every slice because there
   the integrand at `s` is the integrand at zero times the nonzero constant
   `z ^ m`.
2. Absolute summability. The published
   `setIntegral_equalRankIntegrand_determinantSlice` identifies the
   integral of `f` over the `m`-th slice with `a(m) * z ^ m`. After
   rewriting with this identity, `summable_norm_setIntegral_determinantSlice`
   gives `Summable (fun m : ℤ => ‖a(m) * z ^ m‖)`.
3. Expansion. With the same identity,
   `hasSum_setIntegral_determinantSlice` gives
   `HasSum (fun m : ℤ => a(m) * z ^ m) (∫ q, f q ∂μ)`. The right side is
   `equalRankIntegral ψ (normalizedAbsoluteValue T) μ W W' Φ s` by
   definition.

The sum is indexed by all integers `m`. The exponent of `z` is the integer
`m`, so the slice weight is `(q^(-s))^m`. There is no rank shift or
truncation. The `HasSum` conclusion is unconditional convergence of the
series to the actual integral, not a `tsum` identity.

## Scope

The theorem uses only global integrability at the given parameter `s`.
It establishes no unconditional or half-plane convergence, no lower bound
on the support of the determinant slices, no rational continuation, no
existence of an analytic factor, no functional equation and no
multiplicativity. It does not use the normalized quotient Iwasawa measure
identity, representation hypotheses, smoothness or Whittaker type.

## Check

`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` compiles
the module with no errors or warnings. Inspecting
`Langlands.RankinSelberg.equalRankSliceExpansion` shows level parameter `uF`
and only the axioms `propext`, `Classical.choice` and `Quot.sound`.
