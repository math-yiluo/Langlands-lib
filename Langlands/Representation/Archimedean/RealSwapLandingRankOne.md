# Rank-one intertwining integrals as sine-power kernels

Lean module: `Langlands.Representation.Archimedean.RealSwapLandingRankOne`, namespace
`Langlands.Archimedean.RealSwapLandingRankOne`.

## Role and provenance

This module is an internal step in the proof of
`Langlands.Archimedean.RealCharacterInducedFiltrationStatement`. It supplies two
tools for proving the hypothesis `SpecialLanding` of the module `RealSwapLandingAlgebra`:

- a rank-one integral `∫_ℝ F(n̄(y) s g) dy` equals a constant times the sine-power kernel
  operator `C^r_p F (g)` of `RealSwapLandingKernel`, when `F` has a suitable left
  transformation law;
- a function in the principal series transforms under left translation by an upper triangular
  matrix by the principal series character of its diagonal.

The substitution `y = cot θ` is standard calculus. The module formalizes no literature
statement, so it has no sources. All declarations are auxiliary lemmas proved here from
Mathlib and Library results.

## Notation

- `GL_N(ℝ)` is `Langlands.GeneralLinear N ℝ`.
- `r_p(θ) = blockRotation N p θ` is the rotation in the coordinates `p, p + 1`
  (`RealBlockRotation`).
- `C^r_p F (g) = kernelOp N p r F g = ∫₀^π sin^r θ F(r_p(θ) g) dθ` (`RealSwapLandingKernel`).
- `principalSeries ℝ N χ` and `principalSeriesCharacter ℝ N χ` are the Library principal series
  (functions `f` with `f(d u x) = (χ δ^{1/2})(d) f(x)` for diagonal `d` and upper unipotent `u`)
  and its character on the diagonal torus (`StandardModule`).

## Declarations

### The substitution `y = cot θ`

- `cotan θ = cos θ / sin θ`.
- `sin_pos_of_mem_Ioo`: `sin θ > 0` for `θ ∈ (0, π)`.
- `hasDerivAt_cotan`: where `sin θ ≠ 0`, the derivative of `cotan` at `θ` is `-1/sin² θ`.
  Proof: the quotient rule and `sin² θ + cos² θ = 1`.
- `cotan_image`: `cotan` maps `(0, π)` onto `ℝ`. For `y ∈ ℝ` the angle `π/2 - arctan y` lies in
  `(0, π)` and its cotangent is `tan(arctan y) = y`.
- `cotan_injOn`: `cotan` is injective on `(0, π)`. If `cos a / sin a = cos b / sin b`, then
  `sin(b - a) = 0` with `b - a ∈ (-π, π)`, so `a = b`.
- `integral_eq_integral_cotan` (**substitution**): for every `G : ℝ → ℂ`,
  `∫_ℝ G(y) dy = ∫_{(0, π)} sin⁻² θ · G(cot θ) dθ`. This is Mathlib's change of variables
  formula for an injective differentiable map on a measurable set
  (`integral_image_eq_integral_abs_deriv_smul`), with `|d cot θ / dθ| = 1/sin² θ`. The formula
  holds as an equality of Bochner integrals with no integrability hypothesis: the change of
  variables formula also identifies the non-integrable cases, where both sides are `0`.

### Rank-one integrals

- `integral_eq_kernelOp` (**rank-one integral**): let `n̄ : ℝ → GL_N(ℝ)`, `s ∈ GL_N(ℝ)`,
  `σ ∈ ℂ`, `p, r ∈ ℕ`, and let `F : GL_N(ℝ) → ℂ` satisfy
  `F(n̄(cot θ) s x) = σ sin^{r+2} θ F(r_p(θ) x)` for every `θ ∈ (0, π)` and every `x`. Then for
  every `g`,
  `∫_ℝ F(n̄(y) s g) dy = σ C^r_p F (g)`.
  Proof: apply the substitution to `G(y) = F(n̄(y) s g)`, then the hypothesis at `x = g`. The
  integrand becomes `sin⁻² θ · σ sin^{r+2} θ F(r_p(θ) g) = σ sin^r θ F(r_p(θ) g)` on `(0, π)`.
  The interval integral over `[0, π]` equals the integral over `(0, π)`. No integrability
  hypothesis is needed.

### Upper triangular left translations in the principal series

- `mul_of_upperTriangular`: let `f ∈ principalSeries ℝ N χ` and let `B ∈ GL_N(ℝ)` be upper
  triangular (`Matrix.BlockTriangular id`) with diagonal entries `B_ii = a_i` for units
  `a_i ∈ ℝˣ`. Then `f(B x) = principalSeriesCharacter ℝ N χ a · f(x)` for every `x`.
  Proof: write `B = D (D⁻¹ B)` with `D = diag(a)` (`Iwasawa.diagonalUnits a`). The matrix
  `D⁻¹ B` is upper triangular with diagonal `a_i⁻¹ a_i = 1`, so it lies in the upper
  unipotent subgroup. The transformation law of the principal series then gives the claim.
