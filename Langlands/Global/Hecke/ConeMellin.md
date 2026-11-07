# A dyadic Mellin functional equation on cones

Module `Langlands.Global.Hecke.ConeMellin`, namespace `Langlands.Global.Hecke`.

This module is the abstract analytic core of the Tate–Hecke argument for the global functional
equation of Hecke `L`-functions: given a theta relation `θ(x) = N(x)⁻¹ θ̂(x)` on a cone, the
Mellin transform of `θ` minus its constant term continues meromorphically to `ℂ` and its value
at `1 - s` is the Mellin transform of the dual side. It is an internal helper; it will be applied
with `E` the mixed space of a number field, `C` a fundamental cone for the units, `N` the absolute
norm, `χ` the archimedean part of a Hecke character and `f`, `g` theta series obtained from
lattice Poisson summation (module `Langlands.Global.Hecke.LatticePoissonGeneral`).

## Provenance

Internal. The argument is the classical one of Hecke and Tate (Tate's thesis, §4.4: split the
zeta integral at `N = 1`, substitute the theta relation on `N ≤ 1`, and integrate the constant
terms explicitly). The formalization replaces surface measures on `{N = 1}` and polar
coordinates by a dyadic decomposition of the cone, so that the constant terms are computed as
geometric series of shell integrals; the resulting function `M` is defined here and is not taken
from the literature. The dual integral is kept in the form `∫_C g χ N^(-s-1)` (no inversion
`x ↦ x⁻¹` on the cone), which is the form in which it will be identified with the dual zeta
integral.

## Definitions

- `DyadicCone E` (for a real normed space `E` with a measurable structure): a function
  `N : E → ℝ` and a set `C : Set E` with fields `measurable_N`, `measurableSet_C`,
  `pos : ∀ x ∈ C, 0 < N x`, `smul_mem : ∀ x ∈ C, ∀ t, 0 < t → t • x ∈ C`,
  `N_smul : ∀ x ∈ C, ∀ t, 0 < t → N (t • x) = t ^ finrank ℝ E * N x` and
  `rank_pos : 0 < finrank ℝ E`.
- `D.level x = ⌈log (N x) / (finrank ℝ E * log 2)⌉`, and the shells
  `D.piece k = {x | x ∈ C ∧ D.level x = k}`, i.e. the points of `C` with
  `2^(n(k-1)) < N x ≤ 2^(nk)`, `n = finrank ℝ E`.
- `D.lower = {x | x ∈ C ∧ N x ≤ 1}` and `D.upper = {x | x ∈ C ∧ 1 < N x}`.
- `D.ThetaData μ` (for a measure `μ` on `E`): a weight `χ : E → ℂ`, a constant `l : ℂ` with
  `l_ne_zero : l ≠ 0` and `χ_two_smul : ∀ x ∈ C, χ ((2 : ℝ) • x) = l * χ x`,
  `integrableOn_χ : IntegrableOn χ (D.piece 0) μ`; functions `f g : E → ℂ` and constants
  `A B : ℂ` with `f_add : ∀ x ∈ C, f x + A = (N x : ℂ)⁻¹ * (g x + B)`; a.e.-strong
  measurability of `f χ` on `D.upper` and of `g χ` on `D.lower`; and, for every real `σ`,
  integrability of `‖f x * χ x‖ * N x ^ σ` on `D.upper` (`integrableOn_f`) and of
  `‖g x * χ x‖ * N x ^ σ` on `D.lower` (`integrableOn_g`).
- For `T : D.ThetaData μ` and `w s : ℂ`, with `n = finrank ℝ E`:
  - `T.ratio w = l * 2 ^ (n * w)` (complex power);
  - `T.J w = ∫ x in D.piece 0, χ x * (N x : ℂ) ^ (w - 1) ∂μ`;
  - `T.Itilde w = (1 - (T.ratio w)⁻¹)⁻¹ * T.J w`;
  - `T.E1 s = ∫ x in D.upper, f x * χ x * (N x : ℂ) ^ (s - 1) ∂μ`;
  - `T.E2 s = ∫ x in D.lower, g x * χ x * (N x : ℂ) ^ (s - 2) ∂μ`;
  - `T.M s = T.E1 s + T.E2 s + B * T.Itilde (s - 1) - A * T.Itilde s`.

## Main results

Holomorphy of integrals of complex powers (for any measure space `X`, measurable set `S`,
measurable `N : X → ℝ` positive on `S`, and `h : X → ℂ` a.e.-strongly measurable on `S`):

- `hasDerivAt_setIntegral_mul_cpow`: if `‖h‖ N^σ` is integrable on `S` for every real `σ`, then
  `z ↦ ∫ x in S, h x * (N x : ℂ) ^ z ∂μ` has derivative `∫ x in S, h x * N x ^ s * log (N x)`
  at every `s`; `differentiable_setIntegral_mul_cpow` is the corresponding differentiability on
  `ℂ`.
- `integrableOn_mul_cpow`: if `‖h‖ N^(Re z)` is integrable on `S`, so is `h N^z`.

Geometric summation over shells (for a Haar measure `μ` on a finite-dimensional `E`, and
`Φ : E → ℂ` integrable on `piece 0` with `Φ (2^k • y) = c^k * Φ y` for `y ∈ C`, `k : ℤ`,
`c ≠ 0`; write `r = 2 ^ n * c`):

- `DyadicCone.setIntegral_piece_of_scaling`: `∫_{piece k} Φ = r^k * ∫_{piece 0} Φ`.
- `DyadicCone.integral_lower_of_scaling`: if `1 < ‖r‖`, then `Φ` is integrable on `D.lower` and
  `∫_{D.lower} Φ = (1 - r⁻¹)⁻¹ * ∫_{piece 0} Φ`.
- `DyadicCone.integral_upper_of_scaling`: if `‖r‖ < 1`, then `Φ` is integrable on `D.upper` and
  `∫_{D.upper} Φ = -(1 - r⁻¹)⁻¹ * ∫_{piece 0} Φ`.

The functional equation (for `T : D.ThetaData μ`, `μ` a Haar measure):

- `ThetaData.meromorphicOn_M`: `MeromorphicOn T.M univ`.
- `ThetaData.M_eq_integral`: if `1 < ‖T.ratio (s - 1)‖`, then `f χ N^(s-1)` is integrable on `C`
  and `T.M s = ∫ x in C, f x * χ x * (N x : ℂ) ^ (s - 1) ∂μ`.
- `ThetaData.M_one_sub_eq_integral`: if `‖T.ratio (1 - s)‖ < 1`, then `g χ N^(-s-1)` is
  integrable on `C` and `T.M (1 - s) = ∫ x in C, g x * χ x * (N x : ℂ) ^ (-s - 1) ∂μ`.
- `ThetaData.exists_re_gt`: there is `σ : ℝ` such that `σ < Re s` implies both
  `1 < ‖T.ratio (s - 1)‖` and `‖T.ratio (1 - s)‖ < 1`; so both integral formulas hold on a right
  half-plane.
- Auxiliary: `ThetaData.lower_integral` (`1 < ‖T.ratio w‖` gives
  `∫_{D.lower} χ N^(w-1) = T.Itilde w`), `ThetaData.upper_integral` (`‖T.ratio w‖ < 1` gives
  `∫_{D.upper} χ N^(w-1) = -T.Itilde w`), `norm_ratio` (`‖T.ratio w‖ = ‖l‖ * 2 ^ (n * Re w)`),
  and differentiability of `ratio`, `J`, `E1`, `E2`.

## Implemented proof

**Holomorphy.** `hasDerivAt_setIntegral_mul_cpow` applies Mathlib's
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` on the unit ball around `s`. For
`|Re z - Re s| ≤ 1` we have `N^(Re z) ≤ N^(Re s + 1) + N^(Re s - 1)` (`rpow_le_add_rpow`) and
`|log N| ≤ N + N⁻¹` (`abs_log_le_add_inv`), so the derivative `h N^z log N` is dominated by
`‖h‖ (N^(Re s + 2) + 2 N^(Re s) + N^(Re s - 2))`, which is integrable by hypothesis. The
pointwise derivative of `z ↦ N^z` is `N^z log N` (`HasDerivAt.const_cpow`).

**Shells.** Homogeneity of `N` gives `level (2^k • x) = level x + k`, so `x ↦ 2^k • x` maps
`piece j` onto `piece (j + k)`; `level x ≤ 0 ↔ N x ≤ 1`, so `D.lower = ⋃_{j ≥ 0} piece (-j)`
and `D.upper = ⋃_{j ≥ 0} piece (j + 1)`, disjoint unions of measurable sets. The change of
variables `Measure.integral_comp_smul` (for a Haar measure, `∫ h(t • y) dμ = |t|^(-n) ∫ h dμ`)
gives `∫_{piece k} h = 2^(kn) ∫_{piece 0} h(2^k • y) dy`, and integrability transfers likewise
(`integrable_comp_smul_iff`). Under the scaling hypothesis this yields
`∫_{piece k} Φ = r^k ∫_{piece 0} Φ` and the same for `‖Φ‖` with `‖r‖`. The norms of the shell
integrals form a convergent geometric series, so `Φ` is integrable on the union
(`integrableOn_iUnion_of_summable_integral_norm`), and `integral_iUnion` with
`tsum_geometric_of_norm_lt_one` gives `∑_{j ≥ 0} r^(-j) = (1 - r⁻¹)⁻¹` on `D.lower` and
`∑_{j ≥ 0} r^(j+1) = r (1 - r)⁻¹ = -(1 - r⁻¹)⁻¹` on `D.upper`.

**Theta data.** Iterating `χ_two_smul` gives `χ (2^k • x) = l^k χ x` for `k : ℤ`, and
`N (2^k • x)^z = (2^(n z))^k N(x)^z`, so `Φ = χ N^(w-1)` scales with `c = l 2^(n(w-1))` and
`r = 2^n c = T.ratio w` (`two_pow_mul_eq_ratio`). On `piece 0` we have
`2^(-n) < N ≤ 1`, hence `N^σ ≤ exp(|σ| n log 2)`, so integrability of `χ` on `piece 0` gives
integrability of `χ N^(w-1)` and of `‖χ‖ N^σ` for every `σ`; this gives `lower_integral`,
`upper_integral`, and holomorphy of `J`. Holomorphy of `E1`, `E2` follows from
`integrableOn_f`, `integrableOn_g`. `M` is then a combination of entire functions and of
`(1 - ratio⁻¹)⁻¹`, so it is meromorphic (`MeromorphicAt` is closed under `+`, `-`, `*`, `⁻¹`).

**`M_eq_integral`.** Since `Re s > Re (s - 1)`, also `1 < ‖T.ratio s‖` (`norm_ratio_le`). On
`D.lower`, the theta relation `f = N⁻¹ (g + B) - A` gives
`f χ N^(s-1) = g χ N^(s-2) + B χ N^((s-1)-1) - A χ N^(s-1)` (using `N^(z-1) = N^z / N`). All
three terms are integrable on `D.lower` (`integrableOn_g` and `lower_integral` at `s - 1` and at
`s`), with integrals `E2 s`, `B Itilde (s-1)` and `A Itilde s`. Adding the integral over
`D.upper`, which is `E1 s`, and using `C = D.lower ∪ D.upper` (disjoint) gives `M s`.

**`M_one_sub_eq_integral`.** Symmetrically, `‖T.ratio (-s)‖ < 1`. On `D.upper`,
`g = N (f + A) - B` gives `g χ N^(-s-1) = f χ N^(-s) + A χ N^(-s) - B χ N^(-s-1)`; the
integrals over `D.upper` of `f χ N^(-s)`, `χ N^(-s)` and `χ N^(-s-1)` are `E1 (1 - s)`,
`-Itilde (1 - s)` and `-Itilde (-s)` (`upper_integral` at `1 - s` and at `-s`). Adding the integral over `D.lower`, which is `E2 (1 - s)`, gives
`M (1 - s)`.

**`exists_re_gt`.** With `λ = log ‖l‖ / log 2` we have `‖l‖ = 2^λ` and
`‖T.ratio w‖ = 2^(λ + n Re w)`. For `Re s > 1 + |λ| / n`, `n (Re s - 1) > |λ|`, so
`λ + n (Re s - 1) > 0` and `λ + n (1 - Re s) < 0`.
