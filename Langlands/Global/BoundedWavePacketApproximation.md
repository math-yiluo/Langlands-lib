# Approximation lemmas for bounded wave packets

Module `Langlands.Global.BoundedWavePacketApproximation` (namespace
`Langlands.Global.BoundedWavePacket`) proves the analysis behind Lapid's
proof of Lemma 10 (Lapid 2011, p.329; registered as
`lapid-2011-asymptotic-inner-product-truncated-eisenstein`). It imports only
Mathlib. The route is Lapid's: approximate `φ` by uniformly bounded smooth
`φ_n` supported in a fixed compact neighbourhood of the support, show that
`Θ_{φ_n}` is Cauchy in `L²`, and identify its limit with `Θ_φ` by pointwise
convergence. The approximation is constructed here, and Lapid's
convergence `φ_n → φ` in `‖·‖_*` is replaced by convergence almost everywhere
with a uniform bound, which feeds the dominated convergence theorem.

## Clamping

`abs_clamp_sub_le`: for `|b| ≤ C`, `|max (-C) (min C a) - b| ≤ |a - b|`
(clamping to `[-C, C]` moves no point farther from a point of `[-C, C]`).
`clampComplex C z` clamps the real and imaginary parts of `z` to `[-C, C]`.
It is continuous, vanishes at `0` for `C ≥ 0`, has norm at most `2C`, and
satisfies `‖clampComplex C z - w‖ ≤ 2 ‖z - w‖` when `‖w‖ ≤ C` (from
`‖u‖ ≤ |Re u| + |Im u|` and `|Re u|, |Im u| ≤ ‖u‖`).

## Smooth approximation

`exists_smooth_integral_norm_sub_le`: let `E` be a finite-dimensional real
normed space, `ν` a finite Borel measure, `S` compact with
`S ⊆ interior N`, and `f : E → ℂ` measurable, bounded by `C` and zero
outside `S`. For every `ε > 0` there is a smooth `g` (`ContDiff ℝ ∞`), zero
outside `N`, bounded by `2C + 1`, with `g - f` integrable and
`∫ ‖g - f‖ dν ≤ ε`. Proof:

1. `f` is integrable, so Mathlib's
   `Integrable.exists_hasCompactSupport_integral_sub_le` (finite measures on
   `E` are regular) gives a continuous compactly supported `g₀` with
   `∫ ‖f - g₀‖ dν ≤ ε/4`.
2. `g₁ = clampComplex C ∘ g₀` is continuous with compact support, hence
   uniformly continuous, bounded by `2C`, and `‖g₁ - f‖ ≤ 2 ‖g₀ - f‖`
   pointwise.
3. `UniformContinuous.exists_contDiff_dist_le` gives a smooth `g₂` with
   `‖g₂ - g₁‖ < δ` everywhere, where `δ = min 1 (ε / (2 (ν(E) + 1)))`.
4. `exists_contDiff_support_eq_eq_one_iff` gives a smooth `χ` with values in
   `[0, 1]`, support `interior N`, and `χ = 1` exactly on `S`. Then
   `g = χ g₂` is smooth, zero outside `N` and bounded by `2C + 1`. Since
   `f = χ f`, `‖g - f‖ ≤ ‖g₂ - f‖ ≤ δ + 2 ‖g₀ - f‖`, and integrating gives
   `∫ ‖g - f‖ dν ≤ δ ν(E) + ε/2 ≤ ε`.

`exists_seq_smooth_tendsto_ae` applies this with `ε = 1/(m+1)`. The
resulting sequence tends to `f` in `L¹(ν)`, hence in measure
(`tendstoInMeasure_of_tendsto_eLpNorm`), and a subsequence converges
`ν`-almost everywhere (`TendstoInMeasure.exists_seq_tendsto_ae`).

## Dominated convergence for functions vanishing outside a set

For a measurable `N` with `σ(N) < ∞`:

- `aestronglyMeasurable_of_restrict_of_zero_off`: a function vanishing
  outside `N` is a.e. strongly measurable if it is so for `σ` restricted to
  `N` (it equals its indicator);
- `integrable_of_bdd_of_zero_off`: such a function, bounded and a.e. strongly
  measurable, is integrable;
- `tendsto_integral_of_bdd_of_zero_off`: if `F i` are a.e. strongly
  measurable, uniformly bounded by `B`, vanish outside `N` and converge
  `σ`-a.e. to `F₀` along a countably generated filter, then
  `∫ F i dσ → ∫ F₀ dσ` (Mathlib's dominated convergence with the bound
  `B · 1_N`).

## `L²` limits

- `eLpNorm_two_eq_ofReal_sqrt`: for `u ∈ L²`,
  `eLpNorm u 2 μ = ofReal ((∫ ‖u‖²)^{1/2})`.
- `memLp_two_and_tendsto_of_cauchy`: if `f m ∈ L²`, `f m → h` pointwise and
  `∫ ‖f m - f k‖² → 0` as `(m, k) → ∞`, then `h ∈ L²` and
  `eLpNorm (f m - h) 2 μ → 0`. Proof: the Cauchy condition holds for
  `eLpNorm`; by Fatou's lemma for `eLpNorm`
  (`Lp.eLpNorm_lim_le_liminf_eLpNorm`),
  `eLpNorm (h - f m) ≤ liminf_k eLpNorm (f k - f m)`, which is small for
  large `m`; finally `h = f m - (f m - h)`. This is Lapid's "it has a limit
  `F` … thus `F = Θ_φ`".
- `tendsto_integral_mul_conj`: `L²` convergence `f m → h`, `f' m → h'` gives
  `∫ f m · conj (f' m) → ∫ h · conj h'` (continuity of the inner product of
  `Lp ℂ 2`, through `L2.inner_def`).
- `tendsto_integral_norm_sq`: `L²` convergence gives
  `∫ ‖f m‖² → ∫ ‖h‖²` (the previous result with `f' = f`, real parts).

## Wave packets

For a measure `σ` on `ℝⁿ`, coefficients `c : ι → ℝⁿ → ℂ` and kernels
`Φ : ι → ℝⁿ → X → ℂ`, `packet σ c Φ g = ∫ ∑ j, c j x · Φ j x g dσ(x)`; for
`Φ j x g = E j (i e(x)) g` this is the wave packet `Θ` of the statements.
`gramForm Gm z = ∑ j, ∑ j', z j · conj (z j') · Gm j j'`, continuous in `z`,
with `‖gramForm Gm z‖ ≤ ∑ j, ∑ j', R² ‖Gm j j'‖` when every `‖z j‖ ≤ R`.

For a compact `N` with `σ(N) < ∞` and kernels with every `x ↦ Φ j x g`
continuous on `N`:

- `aestronglyMeasurable_sum_mul`, `norm_sum_mul_le`, `integrable_sum_mul`:
  for coefficients bounded by `A` and vanishing outside `N`, the integrand
  `∑ j, c j x · Ψ j x` is measurable, bounded by `∑ j, A · max (C_j) 0`
  (`C_j` a bound of `Ψ j` on `N`), and integrable;
- `packet_sub`: `packet σ c Φ g - packet σ c' Φ g = packet σ (c - c') Φ g`.

`packet_core` is the analytic core of Lemma 10. Its hypotheses: smooth
coefficients `cs m`, bounded by `A ≥ 0` and zero outside `N`, converging
`σ`-a.e. to `c`; a Gram matrix `Gm` and a constant `B`; and the smooth bound
(`HB`): every smooth `d` vanishing outside `N` has
`y ↦ packet σ d Φ (out y)` in `L²(μY)` and
`∫ ‖packet σ d Φ (out y)‖² dμY ≤ B · ∫ Re (gramForm Gm (d x)) dσ(x)`. Its
conclusion: `y ↦ packet σ c Φ (out y)` is in `L²(μY)`, the packets of `cs m`
converge to it in `L²`, and it satisfies the same bound. Proof:

1. For each `g`, `packet σ (cs m) Φ g → packet σ c Φ g` by dominated
   convergence (Lapid: "`Θ_{φ_n}` converges pointwise to `Θ_φ` by Lebesgue's
   dominated convergence theorem").
2. `∫ Re (gramForm Gm (cs m x - cs k x)) dσ → 0` as `(m, k) → ∞`, again by
   dominated convergence (bound `∑ j, ∑ j', (2A)² ‖Gm j j'‖` on `N`, limit
   `gramForm Gm 0 = 0` a.e.).
3. By `packet_sub` and `HB` for `d = cs m - cs k`,
   `∫ ‖Θ_{cs m} - Θ_{cs k}‖² ≤ B · (step 2) → 0`: the packets form a Cauchy
   sequence in `L²` (Lapid: "by (4), `Θ_{φ_n}` is a Cauchy sequence").
4. `memLp_two_and_tendsto_of_cauchy` gives `L²` membership and convergence.
5. The bound passes to the limit: `∫ ‖Θ_{cs m}‖² → ∫ ‖Θ_c‖²`
   (`tendsto_integral_norm_sq`) and
   `∫ Re (gramForm Gm (cs m x)) → ∫ Re (gramForm Gm (c x))` (dominated
   convergence), so `le_of_tendsto_of_tendsto'` applies.
