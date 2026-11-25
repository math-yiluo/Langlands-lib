# Fourier coefficients along a block rotation

Module `Langlands.Representation.Archimedean.RealBlockFourierFinite`, namespace
`Langlands.Archimedean.RealBlockFourierFinite`. It imports
`Langlands.Representation.Archimedean.RealBlockRotation` (closed form of the rotations) and
`Langlands.Representation.Archimedean.OrthogonalFinitePolynomial` (polynomiality of
`O(N)`-finite functions).

## Role and provenance

This is internal infrastructure. It makes no claim from the literature and has no sources. It
serves the proof of `Langlands.Archimedean.RealCharacterPairFiltrationStatement`.
In that proof, the maps between principal series are described by the rotation Fourier
coefficients in one pair of block coordinates `p, p + 1`. This module collects the elementary
facts about those coefficients that the proof needs: how they transform under left rotations
and sign matrices, that only finitely many are nonzero on `O(N)`, that they determine the
function on `O(N)`, and that coefficients along disjoint blocks commute. It does not construct
any map between representations.

## Notation

* `Φ_j f (g) = blockFourierCoefficient N p j f g = ∫₀^{2π} f(r_p(θ) g) e^{-ijθ} dθ` is the
  Library definition (`StandardModule`). Here `r_p(θ) = blockRotation N p θ` is the rotation
  by `θ` in the coordinates `p, p + 1` of `GL_N(ℝ)`. The integral is the interval integral,
  so `Φ_j f (g)` is defined for every function `f`, but it is only meaningful for `f`
  integrable along the rotation orbit.
* `O(N)` is `unitaryCompact ℝ N`. "Right `O(N)`-finite" means
  `f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (GL N ℝ)) (unitaryCompact ℝ N)`: the right
  translates of `f` by `O(N)` span a finite-dimensional space.
* `s_i` is `Unitary.toUnits (signReflection N i)`, the diagonal matrix with `-1` at `i` and `1`
  elsewhere.
* `principalSeries ℝ N χ` is the Library space of smooth `f` with
  `f(diag(a) u g) = principalSeriesCharacter ℝ N χ a · f(g)` for `u` upper unipotent. The
  sign results assume `hχ : ∀ i : ℕ, χ i 1 = 1`. The Library definition allows an arbitrary
  `χ : ℕ → ℝˣ → ℂ`, and the hypothesis is what makes the character at the sign vector
  `s_i` equal to `χ i (-1)`. It holds for genuine characters.
* Unless noted, results assume `hp : p + 1 < N`, so that `p, p + 1` are coordinates.

## Definitions

* `expMode k θ = e^{ikθ}` for `k : ℤ`, `θ : ℝ`.
* `coeff k F = ∫₀^{2π} F(θ) e^{-ikθ} dθ`, the `k`-th Fourier coefficient of `F : ℝ → ℂ`.
  By definition `Φ_k f (g) = coeff k (θ ↦ f(r_p(θ) g))`
  (`blockFourierCoefficient_eq_coeff`, proved by `rfl`).
* `trigPoly D`, the complex span in `ℝ → ℂ` of the `expMode k` with `|k| ≤ D`: the
  trigonometric polynomials of degree at most `D`.
* `signVec i : Fin N → ℝˣ`, with `-1` at `i` and `1` elsewhere.

## Results

Fourier coefficients on `[0, 2π]`.

* `integral_exp_int_mul`: `∫₀^{2π} e^{imθ} dθ` is `2π` for `m = 0` and `0` otherwise.
* `coeff_expMode` (orthogonality): `coeff j (expMode k) = 2π` if `k = j`, and `0` otherwise.
* `coeff_add` for continuous `F, G`, `coeff_smul`, `coeff_zero_fun`: linearity.
* `coeff_comp_add`: for `2π`-periodic `F`, `coeff k (θ ↦ F(θ + φ)) = e^{ikφ} coeff k F`.
* `coeff_comp_neg`: for `2π`-periodic `F`, `coeff k (θ ↦ F(-θ)) = coeff (-k) F`.
* Auxiliary: `continuous_expMode`, `expMode_add` (`e^{ijθ} e^{ikθ} = e^{i(j+k)θ}`),
  `expMode_zero_left`, `intervalIntegrable_coeff`, `periodic_exp_neg`.

Trigonometric polynomials.

* `expMode_mem_trigPoly`, `trigPoly_mono`, `const_mem_trigPoly` (constants have degree `0`),
  `cos_mem_trigPoly`, `sin_mem_trigPoly`, and `affine_mem_trigPoly`:
  `θ ↦ a + (cos θ - 1) b + (sin θ) c` lies in `trigPoly 1`.
* `mul_mem_trigPoly`: `trigPoly a · trigPoly b ⊆ trigPoly (a + b)`.
* `exists_eval_mem_trigPoly`: for every `P : MvPolynomial σ ℂ` there is `D` such that for all
  families `x : σ → ℝ → ℂ` with every `x i ∈ trigPoly 1`, the function
  `θ ↦ P(x(θ))` lies in `trigPoly D`. The degree `D` depends only on `P`.
* `continuous_of_mem_trigPoly`: trigonometric polynomials are continuous.
* `coeff_eq_zero_of_mem_trigPoly`: for `F ∈ trigPoly D` and `D < |j|`, `coeff j F = 0`.
* `eq_sum_coeff_of_mem_trigPoly` (inversion): for `F ∈ trigPoly D`,
  `F θ = (2π)⁻¹ Σ_{j ∈ [-D, D]} coeff j F · e^{ijθ}`.

Rotated matrices.

* `rotMatrix_mul_apply`: `(rotMatrix h θ · A)_{ij} = A_{ij} + (cos θ - 1)(P A)_{ij} +
  sin θ (W A)_{ij}`, with `P = blockProj h` and `W = rotationGenerator N p`.
* `entry_blockRotation_mul_mem_trigPoly`: every entry of `r_p(θ) A` is, as a function of
  `θ`, in `trigPoly 1`.

`O(N)`-finite functions. Let `f : GL_N(ℝ) → ℂ` be continuous and right `O(N)`-finite.

* `exists_trigPoly_of_mem_kFiniteVectors`: there is one `D` such that
  `θ ↦ f(r_p(θ) g)` lies in `trigPoly D` for every `g ∈ O(N)`.
* `exists_blockFourierCoefficient_eq_zero` (uniform finiteness): there is `D : ℕ` such that
  `Φ_j f (g) = 0` for all `j` with `D < |j|` and all `g ∈ O(N)`.
* `exists_eq_sum_blockFourierCoefficient`: there is `D` with the vanishing above and
  `f(r_p(θ) g) = (2π)⁻¹ Σ_{j ∈ [-D, D]} Φ_j f (g) e^{ijθ}` for all `g ∈ O(N)` and `θ : ℝ`.
* `finite_support_blockFourierCoefficient`: for `g ∈ O(N)`, `j ↦ Φ_j f (g)` has finite
  support.
* `eq_finsum_blockFourierCoefficient` (reconstruction): for `g ∈ O(N)`,
  `f(g) = (2π)⁻¹ Σᶠ_j Φ_j f (g)`.
* `eq_zero_of_blockFourierCoefficient_eq_zero` (uniqueness): for `g ∈ O(N)`, if
  `Φ_j f (g) = 0` for every `j`, then `f(g) = 0`.

These statements are only about points `g ∈ O(N)`. They say nothing about `Φ_j f (g)` for
other `g ∈ GL_N(ℝ)`.

Left rotation. For every `f : GL_N(ℝ) → ℂ` (no continuity needed):

* `periodic_blockRotation_mul`: `θ ↦ f(r_p(θ) g)` is `2π`-periodic.
* `blockFourierCoefficient_blockRotation_mul`: `Φ_j f (r_p(φ) g) = e^{ijφ} Φ_j f (g)` for all
  `φ : ℝ` and `g`.

Principal series and signs. Let `hχ : ∀ i, χ i 1 = 1` and `f ∈ principalSeries ℝ N χ`.

* `toUnits_signReflection`: `s_i` is the diagonal matrix `diagonalUnits (signVec i)`.
* `principalSeriesCharacter_signVec`: `principalSeriesCharacter ℝ N χ (signVec i) = χ i (-1)`.
* `apply_signReflection_mul`: `f(s_i g) = χ i (-1) · f(g)` (no assumption on `p`).
* `toUnits_signReflection_mul_self`, `toUnits_signReflection_mul_mul_self`: `s_i² = 1`.
* `neg_one_zpow_mul_blockFourierCoefficient`:
  `(-1)^j Φ_j f (g) = χ_p(-1) χ_{p+1}(-1) Φ_j f (g)`, where `χ_p(-1)` means `χ p (-1)`.
* `blockFourierCoefficient_eq_zero_of_parity`: if `(-1)^j ≠ χ_p(-1) χ_{p+1}(-1)`, then
  `Φ_j f (g) = 0` for every `g ∈ GL_N(ℝ)`.
* `blockFourierCoefficient_signReflection_mul_of_mem`: for `i = p` or `i = p + 1`,
  `Φ_j f (s_i g) = χ_i(-1) Φ_{-j} f (g)`.
* `blockFourierCoefficient_signReflection_mul_of_not_mem`: for `i ≠ p` and `i ≠ p + 1`,
  `Φ_j f (s_i g) = χ_i(-1) Φ_j f (g)`.

Here `i : Fin N` and the conditions compare `(i : ℕ)` with `p` and `p + 1`; all these hold
for every `g ∈ GL_N(ℝ)`.

Disjoint blocks. `blockFourierCoefficient_comm`: if `p + 1 < p'` or `p' + 1 < p` and `f` is
continuous, then `Φ^p_j (Φ^{p'}_{j'} f)(g) = Φ^{p'}_{j'} (Φ^p_j f)(g)` for all `j, j'` and
`g`, where `Φ^p` is the coefficient along `r_p`. No bound `p + 1 < N` is assumed.

## Proofs

* `integral_exp_int_mul`: for `m ≠ 0` the antiderivative is `e^{imθ} / (im)`
  (`integral_exp_mul_complex`), and `e^{2πim} = 1` (`Complex.exp_int_mul_two_pi_mul_I`).
  `coeff_expMode` writes the integrand as `e^{i(k-j)θ}` and applies it.
* `coeff_comp_add` rewrites `F(θ + φ) e^{-ikθ} = e^{ikφ} · G(θ + φ)` with
  `G(x) = F(x) e^{-ikx}`. It substitutes `x = θ + φ`
  (`intervalIntegral.integral_comp_add_right`) and moves the interval `[φ, φ + 2π]` back to
  `[0, 2π]` by periodicity of `G` (`Function.Periodic.intervalIntegral_add_eq`).
  `coeff_comp_neg` substitutes `x = -θ` (`intervalIntegral.integral_comp_neg`) and moves
  `[-2π, 0]` back to `[0, 2π]` in the same way.
* `mul_mem_trigPoly`: the product of the two spans lies in the span of the products
  (`Submodule.mul_mem_mul`, `Submodule.span_mul_span`), and `e^{ijθ} e^{ikθ} = e^{i(j+k)θ}`
  with `|j + k| ≤ |j| + |k|`. `exists_eval_mem_trigPoly` is induction on `P`
  (`MvPolynomial.induction_on`): constants have degree `0`, sums take the maximum degree, and
  multiplication by a variable adds `1`.
* `coeff_eq_zero_of_mem_trigPoly` and `eq_sum_coeff_of_mem_trigPoly` are induction over the
  span (`Submodule.span_induction`). For a generator `expMode k`, they follow from
  orthogonality; both sides are linear, and `coeff_add` applies because trigonometric
  polynomials are continuous.
* `entry_blockRotation_mul_mem_trigPoly`: by `blockRotation_val_eq` (RealBlockRotation),
  `r_p(θ) = 1 + (cos θ - 1) P + sin θ W`, so each entry of `r_p(θ) A` has the form of
  `affine_mem_trigPoly`.
* `exists_trigPoly_of_mem_kFiniteVectors`: Library `exists_mvPolynomial_of_mem_kFiniteVectors`
  at the base point `1` gives one polynomial `P` in the entries with `f(k) = P(k)` for every
  `k ∈ O(N)`. For `g ∈ O(N)` and every `θ`, `r_p(θ) g ∈ O(N)`, so
  `f(r_p(θ) g) = P((r_p(θ) g)_{ij})`. The entries lie in `trigPoly 1`, and
  `exists_eval_mem_trigPoly` gives a degree `D` depending only on `P`, hence not on `g`.
  The finiteness, inversion, reconstruction and uniqueness results then follow from the
  trigonometric polynomial results, with the inversion formula at `θ = 0` for
  reconstruction (`r_p(0) = 1`, `blockRotation_zero`) and `finsum_eq_sum_of_support_subset`
  for the finite sum.
* Left rotation: `r_p(θ) r_p(φ) = r_p(θ + φ)` (`blockRotation_add`), so
  `θ ↦ f(r_p(θ) r_p(φ) g)` is the shift by `φ` of `θ ↦ f(r_p(θ) g)`. That function is
  `2π`-periodic by `blockRotation_add_two_pi`, so `coeff_comp_add` applies.
* `principalSeriesCharacter_signVec`: every entry of `signVec i` has norm `1`, so the modulus
  factors are `1`; the factors `χ k 1` with `k ≠ i` are `1` by `hχ`, leaving `χ i (-1)`.
  `apply_signReflection_mul` is the principal series equivariance at `a = signVec i` and
  `u = 1`.
* Parity: by left rotation with `φ = π`, `Φ_j f (r_p(π) g) = (-1)^j Φ_j f (g)`. Since
  `r_p(θ) r_p(π) = r_p(π) r_p(θ)` and `r_p(π) = s_p s_{p+1}` (`blockRotation_pi`), applying
  `apply_signReflection_mul` twice inside the integral gives
  `Φ_j f (r_p(π) g) = χ_p(-1) χ_{p+1}(-1) Φ_j f (g)`. If `(-1)^j` differs from that product,
  the coefficient is `0`.
* Signs in the block: `s_i r_p(θ) s_i = r_p(-θ)` for `i ∈ {p, p + 1}`
  (`signReflection_mul_blockRotation_mul_of_mem`, RealBlockRotation), so
  `f(r_p(θ) s_i g) = f(s_i r_p(-θ) g) = χ_i(-1) f(r_p(-θ) g)`, and `coeff_comp_neg` turns the
  reflection `θ ↦ -θ` into `j ↦ -j`. Outside the block, `s_i` commutes with `r_p(θ)`
  (`signReflection_mul_blockRotation_mul_of_not_mem`) and the factor `χ_i(-1)` comes out of
  the integral.
* Disjoint blocks: both sides are iterated integrals over `[0, 2π]²` of
  `f(r_{p'}(φ) r_p(θ) g) e^{-ij'φ} e^{-ijθ}`, up to the order of the rotations. The integrand
  is continuous, hence integrable on the compact square, and Fubini
  (`MeasureTheory.intervalIntegral_intervalIntegral_swap`) exchanges the integrals. The
  rotations commute by `blockRotation_commute` (RealBlockRotation).
