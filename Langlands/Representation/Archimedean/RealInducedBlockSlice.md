# Rotations of upper triangular blocks and the one-block bound for induced blocks

Lean module: `Langlands.Representation.Archimedean.RealInducedBlockSlice`.

Worker 5220 wrote this module for Task 6749 (`5dd3db87-6f14-4d0f-b9a7-3d0065415fd8`), the proof
of `RealStandardLanglandsQuotientStatement` (module `RealLargeLanglandsQuotientReduction`). It
bounds the block Fourier coefficients of functions that transform like an induced
(discrete-series) block `D_m` of a real standard module. The bound depends only on the
exponents of that block. This module handles one block; the multi-block bound is built on it.

Notation: `GL_N(ℝ)` is `Langlands.GeneralLinear N ℝ`. For `h : p + 1 < N`, the indices `ia h = p`
and `ib h = p + 1` come from the Library module `RealBlockRotation`. `r_p(θ)` is the Library
rotation `blockRotation N p θ`, which is `[[cos θ, −sin θ], [sin θ, cos θ]]` on the coordinates
`p, p + 1` and the identity elsewhere (`RealBlockRotation.blockRotation_apply`).
`Φ_j F (g) = ∫₀^{2π} F(r_p(θ) g) e^{−ijθ} dθ` is the Library `blockFourierCoefficient N p j F g`,
and `expMode j φ = e^{ijφ}` is from `RealBlockFourierFinite`. `matrixExpUnit`, `upperUnipotent`
and `RealBlockDerivative.IsExpEquivariant` (module `RealBlockLeftDerivative`) are the Library's.
`wave` and `norm_integral_le` come from `RealInducedBlockContour`. Unprefixed names below are in
the namespace `Langlands.Archimedean.RealInducedBlockSlice`.

## Definitions

* `upperUnit h v`: the upper unipotent matrix `1 + v E_{p,p+1}`, as an element of `GL_N(ℝ)`
  with inverse `1 − v E_{p,p+1}`.
* `diagVec h x y`: the vector with `x` at `p`, `y` at `p + 1` and `0` elsewhere.
* `blockB h x y w = exp(diag(diagVec h x y)) · upperUnit h (w e^{−x})`. This is the matrix that
  is `[[e^x, w], [0, e^y]]` on the block and the identity elsewhere. Write `b(x, y, w)`.
* `diagEntry h x y i = exp(diagVec h x y i)`.
* `IsBlockCovariant h α β F` for `α, β ∈ ℂ`, `F : GL_N(ℝ) → ℂ`:
  `F(b(x, y, w) g) = e^{αx + βy} F(g)` for all real `x, y, w` and all `g`.
* `blockMat h a b c d`: the real `N × N` matrix that is `[[a, b], [c, d]]` on the block and the
  identity elsewhere.
* `rotZ x y w θ = (e^y cos θ + w sin θ) + i e^x sin θ ∈ ℂ`. This is the last row
  `(e^x sin θ, e^y cos θ + w sin θ)` of the block of `r_p(θ) b(x, y, w)`, read as a complex
  number. Write `Z`, `ρ = |Z|`, `C = Re Z / ρ`, `S = Im Z / ρ`.
* `rotW x y w θ = cos θ · e^x · S + (w cos θ − e^y sin θ) · C`.
* `waveU x y w = ((e^x + e^y) − i w)/2` and `waveW x y w = ((e^y − e^x) + i w)/2`.
* `modeTerm x y w M j θ = ρ^{−(M+1)} (Z/ρ)^j` with `Z = rotZ x y w θ`.

## Results

Matrices.

* `single_mul_single_self`: `E_{p,p+1} E_{p,p+1} = 0`.
* `upperUnit_apply`, `upperUnit_mem`: the entries of `upperUnit h v`; it lies in
  `upperUnipotent N ℝ`.
* `sum_mul_diagVec`: `Σ_i α_i · diagVec h x y i = α_p x + α_{p+1} y`.
* `blockB_apply`: the `(i, j)` entry of `b(x, y, w)` is `diagEntry h x y i` if `i = j`, plus
  `w` if `(i, j) = (p, p + 1)`, and `0` otherwise.
* `blockMat_mul`: block matrices multiply like `2 × 2` matrices.
* `blockRotation_eq_blockMat`: `r_p(θ) = blockMat h (cos θ) (−sin θ) (sin θ) (cos θ)`.
* `blockB_eq_blockMat`: `b(x, y, w) = blockMat h e^x w 0 e^y`.

Covariance.

* `isBlockCovariant_of_isExpEquivariant`: if `IsExpEquivariant α F`, i.e.
  `F(exp(diag x) u g) = e^{Σ α_i x_i} F(g)` for upper unipotent `u`, then
  `IsBlockCovariant h α_p α_{p+1} F`.

Rotations.

* `rotZ_re`, `rotZ_im`, `rotZ_ne_zero`: the real and imaginary parts of `Z`, and `Z ≠ 0`.
* `blockRotation_mul_blockB` (Iwasawa decomposition of `r_p(θ) b(x, y, w)`):

  `r_p(θ) b(x, y, w) = b(x + y − log ρ, log ρ, rotW x y w θ) · r_p(arg Z)`.

* `apply_blockRotation_mul_blockB`: if `IsBlockCovariant h α β F`, then
  `F(r_p(θ) b(x, y, w) g) = exp(α (x + y − log ρ) + β log ρ) · F(r_p(arg Z) g)`.

The one-block bound (section `Bound`).

* `rotZ_eq_wave`: `Z(θ) = wave (waveU x y w) (waveW x y w) θ`, i.e. `Z = u e^{iθ} + w' e^{−iθ}`
  with `u = waveU x y w` and `w' = waveW x y w`.
* `waveU_re`, `le_norm_waveU`, `norm_waveU_pos`: `Re u = (e^x + e^y)/2 ≤ |u|`, and `|u| > 0`.
* `norm_waveW_lt`: `|w'| < |u|`.
* `ofReal_norm_ne_zero`: `(|Z| : ℂ) ≠ 0` for `Z ≠ 0`.
* `mode_pos`, `mode_neg`: for `Z ≠ 0`,
  `ρ^{−(M+1)} (Z/ρ)^{M+1+2l} = Z^l / conj(Z)^{l+M+1}` and
  `ρ^{−(M+1)} (Z/ρ)^{−(M+1+2l)} = conj(Z)^l / Z^{l+M+1}`.
* `expMode_arg`: `e^{ij arg Z} = (Z/ρ)^j`.
* `exp_covariance_factor`: if `α = β + (M + 1)` and `ρ > 0`, then
  `exp(α (s − log ρ) + β log ρ) = e^{αs} ρ^{−(M+1)}`.
* `continuous_rotZ`, `continuous_modeTerm`: continuity in `θ`.
* `contour_bound_le`: for `|u| > 0`, the right side of the contour bound with `n = l + M + 1`
  is at most `2π · 2^{|N|} 2^l 2^{l+M+1} / |u|^{M+1}`.
* `norm_integral_modeTerm_le`: if `j = ±(M + 1 + 2l)`, then
  `|∫₀^{2π} modeTerm x y w M j θ · e^{−i j₀ θ} dθ| ≤ 2π · 2^{|j₀|} 2^l 2^{l+M+1} / |u|^{M+1}`.
* `norm_waveU_sq`: `|u|² = ((e^x + e^y)² + w²)/4`.
* `exp_half_le_norm_waveU`: `e^{(x+y)/2} ≤ |u|`.
* `exp_div_norm_waveU_le`: for real `a`,
  `e^{a(x+y)} / |u|^{M+1} ≤ e^{(a − M/2)(x+y)} / |u|`.
* `norm_blockFourierCoefficient_blockB_le` (**one-block bound**). Assume:
  * `α = β + (M + 1)` with `M ∈ ℕ`, and `IsBlockCovariant h α β F`;
  * `g ∈ GL_N(ℝ)`, a finite set `S ⊆ ℤ` and `c : ℤ → ℂ` with
    `F(r_p(φ) g) = (2π)⁻¹ Σ_{j ∈ S} c_j e^{ijφ}` for all real `φ`;
  * `|j| ≤ D` for `j ∈ S`;
  * for `j ∈ S` with `c_j ≠ 0` there is `l ∈ ℕ` with `j = M + 1 + 2l` or `j = −(M + 1 + 2l)`.

  Then for all `j₀ ∈ ℤ` and real `x, y, w`:

  `|Φ_{j₀} F (b(x, y, w) g)| ≤ 2^{|j₀| + 2D} (Σ_{j ∈ S} |c_j|) · e^{(Re α − M/2)(x + y)} / |u|`,

  where `u = waveU x y w = ((e^x + e^y) − i w)/2`.

## Proofs

`upperUnit` is invertible because `E_{p,p+1}² = 0`. `blockB_apply` combines
`RealPrincipalSeriesDuality.matrixExpUnit_diagonal` (the exponential of a diagonal matrix is the
diagonal matrix of exponentials) with `upperUnit_apply`; the entry `e^x · w e^{−x}` simplifies to
`w`. `blockMat_mul` computes the matrix product entrywise: for a row index in the block the sum
over `k` has only the two block terms (`Fintype.sum_eq_add`), and other rows are rows of the
identity. `blockRotation_eq_blockMat` and `blockB_eq_blockMat` compare entries using
`blockRotation_apply` and `blockB_apply`. `isBlockCovariant_of_isExpEquivariant` applies
`IsExpEquivariant` to `x = diagVec h x y` and `u = upperUnit h (w e^{−x})` and rewrites the
exponent by `sum_mul_diagVec`.

`blockRotation_mul_blockB`: both sides are block matrices, by `blockRotation_eq_blockMat`,
`blockB_eq_blockMat` and `blockMat_mul`. `Complex.cos_arg` and `Complex.sin_arg` give
`cos(arg Z) = C` and `sin(arg Z) = S`. The four block entries are then rational identities in
`e^x, e^y, w, cos θ, sin θ, ρ`. They follow from `ρ² = (e^y cos θ + w sin θ)² + (e^x sin θ)²` and
`sin² θ + cos² θ = 1` (`field_simp` with `linear_combination`). `apply_blockRotation_mul_blockB`
is this identity followed by block covariance.

`rotZ_eq_wave` expands `e^{±iθ} = cos θ ± i sin θ`. `norm_waveW_lt` computes
`|u|² = ((e^x + e^y)² + w²)/4` and `|w'|² = ((e^y − e^x)² + w²)/4`; their difference is
`e^x e^y > 0`. `mode_pos` and `mode_neg` use `ρ² = Z · conj(Z)` (`Complex.mul_conj'`), and
`expMode_arg` uses `|Z| e^{i arg Z} = Z`. `exp_covariance_factor` rewrites the exponent as
`αs − (M + 1) log ρ`.

`norm_integral_modeTerm_le`: for `j = M + 1 + 2l`, `mode_pos` and `rotZ_eq_wave` turn the
integrand into `X^l / conj(X)^{l+M+1} · e^{−i j₀ θ}` with `X = wave u w'`. The contour bound
`RealInducedBlockContour.norm_integral_le` (`n = l + M + 1`, `N = −j₀`, using `|w'| < |u|`) and
`contour_bound_le` give the claim. For `j = −(M + 1 + 2l)` the integrand is the complex conjugate
of the case `N = j₀`, by `mode_neg`; Mathlib's `intervalIntegral.intervalIntegral_conj` moves the
conjugation out of the integral. `contour_bound_le` bounds `(1/2)^{(M+1)+N}` by `2^{|N|}` and
`(5/4)^l / (3/4)^{l+M+1}` by `2^l 2^{l+M+1}`.

`norm_waveU_sq` computes `|u|²` from the real and imaginary parts. `exp_half_le_norm_waveU`
compares squares: `e^{x+y} = e^x e^y ≤ ((e^x + e^y)² + w²)/4` because `(e^x − e^y)² ≥ 0`.
`exp_div_norm_waveU_le`: `e^{(M/2)(x+y)} = (e^{(x+y)/2})^M ≤ |u|^M` by `exp_half_le_norm_waveU`,
and `e^{a(x+y)} = e^{(a − M/2)(x+y)} · e^{(M/2)(x+y)}`; cross-multiply.

`norm_blockFourierCoefficient_blockB_le`: by `apply_blockRotation_mul_blockB`, the expansion
`hexp` at `φ = arg Z`, `exp_covariance_factor` (with `s = x + y`) and `expMode_arg`,

`F(r_p(θ) b(x, y, w) g) = Σ_{j ∈ S} e^{α(x+y)} (2π)⁻¹ c_j · modeTerm x y w M j θ`.

So `Φ_{j₀} F (b(x, y, w) g) = Σ_j K_j I_j`, where `K_j = e^{α(x+y)} (2π)⁻¹ c_j` and `I_j` is
the integral of `norm_integral_modeTerm_le` (`intervalIntegral.integral_finsetSum`; each term is
continuous). Terms with `c_j = 0` vanish. Otherwise `j = ±(M + 1 + 2l)` with `l + M + 1 ≤ D`
(from `|j| ≤ D`), so `2^l 2^{l+M+1} ≤ 2^D 2^D`. This gives
`|K_j I_j| ≤ |c_j| · 2^{|j₀| + 2D} e^{Re α (x+y)} / |u|^{M+1}`. Summing over `S` and applying
`exp_div_norm_waveU_le` with `a = Re α` gives the bound.

## Use

In the Library's `realStandardModule`, an induction block of weight `m` with `M = |m|` at
positions `p, p + 1` has position characters `sgn^{M+1} |·|^{t+M/2}` and `|·|^{t−M/2}`. So the
`ρ`-shifted exponents `α_p, α_{p+1}` (`RealBlockDerivative.isExpEquivariant_of_mem_principalSeries`)
satisfy `α_p − α_{p+1} = M + 1`. The modes `j` of `φ ↦ F(r_p(φ) g)` satisfy
`(−1)^j = (−1)^{M+1}`, because `r_p(φ + π) = −1` on the block times `r_p(φ)`. The module's
Fourier condition removes the modes `|j| < M`. So the remaining modes are exactly
`±(M + 1 + 2l)`, as `hmode` requires. Since `|u| ≥ (e^x + e^y)/2 ≥ e^y/2`, the right side is at
most `2^{|j₀| + 2D + 1} (Σ |c_j|) exp((Re α − M/2) x + (Re α − M/2 − 1) y)`. The exponents
`Re α − M/2` at `p` and `Re α − M/2 − 1` at `p + 1` equal `Re(α_p + α_{p+1})/2 + 1/2` and
`Re(α_p + α_{p+1})/2 − 1/2`. These are the tied exponents of the block (equal real parts after
removing the `ρ`-shift `1/2, −1/2`). So `D_m` behaves like a tied pair of characters, the case
handled for character lists by `RealCharacterLanglandsQuotient`. The sharper form with `|u|` is
kept because it is also bounded by a multiple of the rotation average
`∫₀^{2π} e^{(Re α − M/2)(x' + y')} e^{−y'} dθ` of the tied exponential at
`r_p(θ) b(x, y, w) = b(x', y', w') r_p(arg Z)` (here `e^{y'} = |Z| ≤ 2|u|`). The weaker form
is not bounded by that average as `y → −∞`.

## Provenance

This is derived, internal infrastructure for Task 6749. The Iwasawa decomposition of
`r_p(θ) b(x, y, w)` is elementary `GL_2(ℝ)` linear algebra. The bound is an explicit form of the
standard fact that `K`-finite matrix coefficients of discrete series of `GL_2(ℝ)`, here functions
in the induced model, decay like the tempered exponent. The proof via the contour bound is this
module's own; no literature statement is formalized here.
