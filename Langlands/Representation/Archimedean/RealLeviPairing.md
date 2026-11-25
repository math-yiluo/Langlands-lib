# The pairing along a standard parabolic subgroup, integrated over the torus of induction blocks

Lean module: `Langlands.Representation.Archimedean.RealLeviPairing`.

This module is part of the proof of `RealStandardLanglandsQuotientStatement` (module
`RealLargeLanglandsQuotientReduction`). It is
the first of three modules (`RealLeviPairing`, `RealLeviBump`, `RealLeviNonvanishing`) for the
nonvanishing step of the single-shot Langlands-quotient argument. The entry statement of the
three modules is `RealLeviNonvanishingStatement` (see `RealLeviNonvanishing.md`). This module
states no `Prop`-valued statement of its own. It defines the pairing `Θ` that appears in
`RealLeviLimitStatement` and proves its analytic properties. No literature statement is claimed
and nothing is cited; the provenance is internal ("derived"). Unprefixed names below are in the
namespace `Langlands.Archimedean.RealLeviPairing`.

## Notation

From earlier modules:

* `RealLeviChartIntegralStatement` (namespace `RealLeviChart`): for block sizes
  `sz : Fin c → ℕ` and `N = ∑_i sz_i`, `cls sz p` is the block of the position `p`, `Coord sz`
  the set of pairs `(p, q)` with `cls q < cls p`, `lower sz X` the lower unipotent matrix with
  entries `X` below the diagonal blocks, and `lowerGL sz X = n̄(X)` its unit in `GL_N(ℝ)`.
  `blockDiagGL sz κ = diag(κ_0, …, κ_{c-1})`.
* `RealLeviLimit`: `bdK sz κ = blockDiagGL sz κ` for `κ ∈ K_M = ∏_i O(sz_i)`.
* `RealInducedStandardBound`: `slots ds N`, the slots of the induction blocks of `ds`.
  `realPositionBlockExponent ds p` is the real part of the exponent of the block of `ds` at the
  position `p`.
* `RealInducedTorusCore`: `zeroModes L` sets all modes of `L` to `0`, and `withModes L J` sets
  them to the entries of `J`.
* `RealInducedBlockBound`: `coeffs L F g` is the iterated block Fourier coefficient along `L`.
  Each step is the Library's `blockFourierCoefficient`, `∫₀^{2π} F(r_p(θ) g) e^{-ijθ} dθ`, which
  is not normalized (no factor `1/(2π)`).
* `RealLeviTorus`: `torusElem L θ` (for `θ : Fin L.length → ℝ`) is the product of the block
  rotations `r_{p_i}(θ_i)` of the slots `(p_i, j_i)` of `L`. `torusMeasure r` is the product
  `Measure.pi` of `r` copies of Lebesgue measure restricted to `(0, 2π]`. It is not normalized:
  its total mass is `(2π)^r`. `coeffs_eq_integral`: for continuous `F`,
  `coeffs (zeroModes L) F g = ∫ F(torusElem L θ · g) d(torusMeasure L.length)(θ)`. This torus
  integral is `(2π)^{|L|}` times the average of `F(torusElem L θ · g)` over the angles.
* `RealLeviModes`: joint allowedness (`M ≤ |j|` at every slot), `HasDegree`,
  `coeffs_zeroModes_mul_eq_sum` (Parseval for a product along the slots) and
  `window_of_mem_standard` (a vector of the standard module has vanishing block coefficients of
  modes `|j| < M`).

## Definitions

* `psi L u h κ X = coeffs (zeroModes L) (x ↦ u(x · diag κ) · h(x · n̄(X) · diag κ)) 1`, i.e.
  `c_Z(x ↦ u(x diag(κ)) h(x n̄(X) diag(κ)))`.
* `theta L u h = ∫_{K_M} ∫_{Coord sz → ℝ} psi L u h κ X dX dκ`, with the product of the
  normalized Haar measures `haarK (sz i)` on `K_M` and Lebesgue measure on the coordinates. For
  `L = slots ds N` this is the left side of the conclusion of `RealLeviLimitStatement`.
* `Admissible sz ds` (structure, a `Prop`): `realRank ds = ∑_i sz_i`, the exponents
  `realPositionBlockExponent ds` decrease weakly along the positions (`anti`), and they decrease
  strictly from a block of `Q` to any later block (`strict`). These are the hypotheses of
  `RealLeviLimitStatement`.

## Results

**Iterated coefficients** (section `Coeffs`).

* `coeffs_zero_fun`: the coefficients of `0` vanish.
* `coeffs_eq_zero_of_forall`: if the slots of `L` are pairwise disjoint and for one slot `t ∈ L`
  the block coefficient of `F` at `(t.p, t.j)` vanishes everywhere, then `coeffs L F` vanishes
  everywhere.
* `coeffs_const_mul`: `coeffs L (a · F) = a · coeffs L F`.
* `hasDegree_mono`: `HasDegree S D u` implies `HasDegree S D' u` for `D ≤ D'`.
* `exists_bound_compact`: a continuous `F` is bounded on `O(N) · S` for compact `S`.

**The pairing** (section `Pairing`). Throughout, `u` is an `O(N)`-finite vector of
`principalSeries ℝ N (dualChar (realPositionCharacter ds))` and `h` an `O(N)`-finite vector of
`realStandardModule N ds`.

* `gramBound_mono`: `gramBound a ≤ gramBound b` if `a_l ≤ b_l` for all `l > 0` (the Gram
  determinants are `≥ 1`, and the factor at `l = 0` is `1`).
* `psi_eq_integral`: for continuous `u`, `h`, `psi` is the torus integral
  `∫ u(τ_θ diag κ) h(τ_θ n̄(X) diag κ) d(torusMeasure L.length)(θ)`, with `τ_θ = torusElem L θ`
  and the unnormalized `torusMeasure` (total mass `(2π)^{|L|}`).
* `continuous_psi`: `(κ, X) ↦ psi L u h κ X` is continuous (dominated convergence with the bound
  of `u`, `h` on compact sets).
* `exists_dom` (domination): assuming `RealLeviChartIntegrableStatement` and `Admissible sz ds`,
  there is an integrable function `D` of `X`, bounded above, with `‖psi (slots ds N) u h κ X‖ ≤
  D(X)` for all `κ`, `X`. Proof: the two-point bound `exists_bound` of `RealInducedStandardBound`
  bounds `‖psi‖` by a constant times `‖c_Z(e^{-t}(x y_1) e^{t}(x y_2))‖` with `y_1 = diag κ`,
  `y_2 = n̄(X) diag κ`, where `t = realPositionBlockExponent ds`. Since `τ_θ diag κ` is
  orthogonal, `e^{-t}(τ_θ y_1) = 1`. Since `τ_θ n̄(X) = n̄(Ad(τ_θ) X) τ_θ` (`mul_lowerGL` of
  `RealLeviGeometry`; the torus elements `τ_θ` lie in the block orthogonal group because the
  induction blocks lie inside the blocks of `Q`), `norm_expFun_le` of `RealLeviLimit` bounds the
  second factor by `gramBound γ (Ad(τ_θ) X)` with `γ_l = gammaExp t l` (`gramBound_mono`). Then
  `D(X) = C ∫ gramBound γ (Ad(τ_θ) X) d(torusMeasure)(θ)` is integrable by
  `RealLeviChartIntegrableStatement` (its hypotheses on `γ` come from `anti` and `strict`) and
  `integrable_comp_adCoord` of
  `RealLeviLimit`, and `D` is bounded because `gramBound γ ≤ 1` (`gramBound_le_one`).
* `integrable_psi_prod`, `integrable_psi`, `integrable_integral_psi`: integrability of `psi` on
  `K_M × (Coord sz → ℝ)`, in `X` for fixed `κ`, and of `κ ↦ ∫_X psi`.
* `psi_add`, `psi_smul`, `theta_add`, `theta_smul`: `psi` and `theta` are additive and
  homogeneous in `h` (`theta_add` uses the integrability results).
* `psi_congr`, `theta_congr` (dependence on `u`): if `u` and `u'` are two such vectors with
  `coeffs (withModes (slots ds N) J) u (diag κ) = coeffs (withModes (slots ds N) J) u' (diag κ)`
  for every jointly allowed `J` of length `|slots ds N|` and every `κ ∈ K_M`, then
  `psi (slots ds N) u h κ X = psi (slots ds N) u' h κ X` for all `κ`, `X`, hence
  `theta (slots ds N) u h = theta (slots ds N) u' h`. Proof: Parseval
  (`coeffs_zeroModes_mul_eq_sum`) writes `psi` as a finite sum over mode lists `J` of
  `coeffs_J u (diag κ) · coeffs_{-J} h (n̄(X) diag κ)`. For `J` not jointly allowed, some slot has
  `|j| < M` and the coefficient of `h` vanishes (`window_of_mem_standard`,
  `coeffs_eq_zero_of_forall`).
