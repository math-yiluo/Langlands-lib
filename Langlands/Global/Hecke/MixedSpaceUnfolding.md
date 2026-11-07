# Measure theory on the mixed space: multiplication, inversion and unfolding over units

Module `Langlands.Global.Hecke.MixedSpaceUnfolding`, namespace `Langlands.Global.Hecke`.

Throughout, `K` is a number field, `V = mixedSpace K = (ℝ^{real places}) × (ℂ^{complex places})`
is its mixed space with the componentwise ring structure and Lebesgue measure `volume`,
`N = mixedEmbedding.norm : V → ℝ` is the norm `N(x) = ∏_w ‖x_w‖^{mult w}`,
`C = fundamentalCone K` is Mathlib's fundamental cone for the action of the units `(𝓞 K)ˣ` on
`V` (by `u • x = mixedEmbedding K u * x`), and `n = [K : ℚ]`.

This module collects the measure-theoretic facts about `V` that the Tate–Hecke argument for the
global functional equation of Hecke `L`-functions needs: multiplicative changes of variables,
the inversion `x ↦ x⁻¹`, the unfolding of an integral over `V` into a sum over units of
integrals over `C`, and the structure of `C` as a dyadic cone in the sense of
`Langlands.Global.Hecke.ConeMellin`. It is an internal helper.

## Provenance

Internal. The facts are standard: the Jacobian of multiplication on `ℝ^{r₁} × ℂ^{r₂}` is the
norm, the Jacobian of inversion is `N(x)⁻²`, and the unit translates `u • C` of a fundamental
cone cover almost every point of the mixed space `#torsion` times. The last fact is the
unfolding step of Hecke's proof of the functional equation (the integral over the mixed space
is folded into an integral over a fundamental domain for the units, as in the passage from the
idele group to the norm-one idele class group in Tate's thesis, §4.4); here it is phrased on the
mixed space instead of on the idele class group. The fundamental cone, its unit-translation
properties (`fundamentalCone.exists_unit_smul_mem`,
`fundamentalCone.unit_smul_mem_iff_mem_torsion`) and its boundedness
(`fundamentalCone.isBounded_normLeOne`) are from Mathlib.

## Definitions

- `mulL y : V →L[ℝ] V`, multiplication `x ↦ y * x` by `y ∈ V`.
- `unitOfNormNeZero (hx : N x ≠ 0) : Vˣ`, a point of nonzero norm as a unit of `V`
  (inverse `x⁻¹`).
- `mulHomeomorph (hy : N y ≠ 0) : V ≃ₜ V`, the homeomorphism `x ↦ y * x` with inverse
  `x ↦ y⁻¹ * x`.
- `fundamentalDyadicCone : DyadicCone V` with `N := mixedEmbedding.norm` and
  `C := fundamentalCone K` (simp lemmas `fundamentalDyadicCone_N`, `fundamentalDyadicCone_C`).
- Instances `Countable K` and `Countable (𝓞 K)ˣ`.

## Main results

Multiplication:

- `det_mulL`: `det (mulL y) = (∏_{w real} y_w) * ∏_{w complex} normSq (y_w)`;
  `abs_det_mulL`: `|det (mulL y)| = N y`; `det_mulL_ne_zero`: `N y ≠ 0 → det (mulL y) ≠ 0`.
- `map_mulL_volume`, `map_mulHomeomorph_volume`: for `N y ≠ 0` the push-forward of `volume`
  under `x ↦ y * x` is `ofReal (N y)⁻¹ • volume`.
- `integral_comp_mul_left`: for `N y ≠ 0` and any `f : V → E` (`E` a real normed space),
  `∫ x, f (y * x) = (N y)⁻¹ • ∫ x, f x`.
- `lintegral_comp_mul_left`: for `N y ≠ 0` and `f : V → ℝ≥0∞`,
  `∫⁻ x, f (y * x) = ofReal (N y)⁻¹ * ∫⁻ x, f x`.

Inversion:

- `normAtPlace_inv`: `normAtPlace w x⁻¹ = (normAtPlace w x)⁻¹`; `norm_inv'`: `N x⁻¹ = (N x)⁻¹`;
  `norm_neg'`: `N (-x) = N x`.
- `mul_inv_cancel_of_norm_ne_zero`: `N x ≠ 0 → x * x⁻¹ = 1`.
- `isOpen_setOf_norm_ne_zero`, `measurableSet_setOf_norm_ne_zero` for `{x | N x ≠ 0}`.
- `hasFDerivAt_inv'`: if `N x ≠ 0`, then `y ↦ y⁻¹` has Fréchet derivative
  `mulL (-(x⁻¹ * x⁻¹))` at `x`.
- `volume_setOf_norm_eq_zero`: `volume {x | N x = 0} = 0`; hence `ae_norm_ne_zero`
  (`∀ᵐ x, N x ≠ 0`) and `setOf_norm_ne_zero_ae_eq_univ`.
- `integral_comp_inv`: for any `g : V → E`, `∫ x, (N x)⁻¹ ^ 2 • g x⁻¹ = ∫ x, g x`.

Units:

- `unit_smul_eq_mul`: `u • x = mixedEmbedding K u * x`;
  `norm_mixedEmbedding_unit_ne_zero`: `N (mixedEmbedding K u) ≠ 0`.
- `measurePreserving_unit_smul u`: `x ↦ u • x` preserves `volume`;
  `measurableEmbedding_unit_smul u`: it is a measurable embedding.
- `setOf_unit_smul_mem_eq`: if `u₀ • x ∈ C`, then `{u | u • x ∈ C} = torsion · u₀`.
- `tsum_indicator_unit_smul`: if `N x ≠ 0`, then
  `∑' u, indicator_C 1 (u • x) = torsionOrder K` in `ℝ≥0∞`;
  `hasSum_indicator_unit_smul`: the same as a real `HasSum`;
  `tsum_indicator_inv_smul`, `hasSum_indicator_inv_smul`: the same with `u⁻¹ • x`;
  `measurable_indicator_inv_smul`: `y ↦ indicator_C 1 (u⁻¹ • y)` is measurable.

Unfolding over the units:

- `setLIntegral_unit_smul`: `∫⁻ x in C, Ψ (u • x) = ∫⁻ y, indicator_C 1 (u⁻¹ • y) * Ψ y`.
- `tsum_setLIntegral_unit_smul`: for `Ψ : V → ℝ≥0∞` a.e.-measurable,
  `∑' u, ∫⁻ x in C, Ψ (u • x) = torsionOrder K * ∫⁻ x, Ψ x`.
- `setIntegral_unit_smul`: `∫ x in C, Ψ (u • x) = ∫ y, indicator_C 1 (u⁻¹ • y) • Ψ y`.
- `hasSum_setIntegral_unit_smul`: for `Ψ : V → E` integrable,
  `HasSum (fun u => ∫ x in C, Ψ (u • x)) (torsionOrder K • ∫ x, Ψ x)`.

Coordinates on the fundamental cone:

- `normAtPlace_le_norm`: `normAtPlace w x ≤ ‖x‖` (sup norm of `V`).
- `exists_normAtPlace_bounds`: there are `r, R > 0` such that for all `x ∈ C` and all
  infinite places `w`,
  `r * N(x) ^ (1/n) ≤ normAtPlace w x ≤ R * N(x) ^ (1/n)`, where `n = finrank ℚ K` and the power
  is the real power with exponent `(n : ℝ)⁻¹`.

## Implemented proof

**Determinant.** `mulL y` is, as a linear map, the product map of the coordinatewise maps
`t ↦ y_w t` on the real and complex factors (`mulL_toLinearMap`); `LinearMap.det_prodMap` and
`LinearMap.det_pi` give the product of the determinants, and the determinant of `t ↦ z t` on
`ℂ` over `ℝ` is `Algebra.norm ℝ z = normSq z`. Taking absolute values, the real factors give
`∏ |y_w| = ∏ normAtPlace w y` (multiplicity 1) and the complex factors give
`normSq y_w = ‖y_w‖^2` (multiplicity 2); reindexing the product over places by the
real/complex subtypes gives `N y`.

**Multiplicative change of variables.** `Measure.map_linearMap_addHaar_eq_smul_addHaar` gives
`map (mulL y) volume = ofReal |det|⁻¹ • volume`. Then `integral_map_equiv` (resp.
`lintegral_map_equiv`) for the measurable equivalence underlying `mulHomeomorph`, together with
`integral_smul_measure` (resp. `lintegral_smul_measure`), gives the two formulas.

**Inversion.** Where `N x ≠ 0`, `x` is a unit of the ring `V`; inversion agrees near `x` with
`Ring.inverse`, whose derivative at a unit `a` is `h ↦ -(a⁻¹ h a⁻¹)` (`hasFDerivAt_ringInverse`);
by commutativity this is `mulL (-(x⁻¹ * x⁻¹))`. The set `{N = 0}` is the union over places of
coordinate hyperplanes (real places: `mixedEmbedding.volume_eq_zero`; complex places: the
kernel of a nonzero `ℝ`-linear map, a proper subspace, `Measure.addHaar_submodule`), so it is
null. On the open set `U = {N ≠ 0}`, inversion is injective and maps `U` onto `U`, so the
change of variables formula `integral_image_eq_integral_abs_det_fderiv_smul` gives
`∫_U g = ∫_U |det mulL(-(x⁻¹x⁻¹))| • g(x⁻¹)`, and `|det mulL(-(x⁻¹ x⁻¹))| = N(x⁻¹)^2 = N(x)⁻²`.
Since `U` is conull, both sides are integrals over `V`.

**Units.** `u • x = mixedEmbedding K u * x` and `N (mixedEmbedding K u) = 1` (`norm_unit`), so
by the multiplicative change of variables `x ↦ u • x` preserves `volume`. `K` is countable as a
finite-dimensional `ℚ`-vector space, hence so are `𝓞 K` and `(𝓞 K)ˣ`.

**Counting.** If `N x ≠ 0`, Mathlib gives `u₀` with `u₀ • x ∈ C`, and
`fundamentalCone.unit_smul_mem_iff_mem_torsion` says that `ζ • (u₀ • x) ∈ C` iff `ζ` is
torsion. Writing `u = (u u₀⁻¹) u₀` shows `{u | u • x ∈ C} = torsion · u₀`, a set in bijection
with the torsion subgroup (right multiplication by `u₀`), so the sum of the indicator values is
its cardinality `torsionOrder K` (`ENNReal.tsum_const`, `ENat.card_congr`). The real version
follows by `ENNReal.hasSum_toReal`, since every term is `0` or `1`; the `u⁻¹` versions follow by
reindexing with `Equiv.inv`.

**Unfolding.** By the measure-preserving embedding `x ↦ u • x`,
`∫⁻_C Ψ(u • x) = ∫⁻ indicator_C(u⁻¹ • y) Ψ(y) dy` (and likewise for Bochner integrals). For
nonnegative `Ψ`, `lintegral_tsum` exchanges the sum over the countable unit group with the
integral, and for a.e. `y` (those with `N y ≠ 0`) the inner sum is
`torsionOrder K * Ψ y` by the counting lemma. For integrable `Ψ`, the functions
`G_u(y) = indicator_C(u⁻¹ • y) • Ψ(y)` are integrable (dominated by `‖Ψ‖`), and the sum of
`∫ ‖G_u‖` is finite because it equals `torsionOrder K * ∫⁻ ‖Ψ‖ₑ` by the nonnegative case; so
`hasSum_integral_of_summable_integral_norm` gives
`HasSum (fun u => ∫ G_u) (∫ ∑' u, G_u)`, and the integrand `∑' u, G_u(y)` is a.e.
`torsionOrder K • Ψ(y)` by the counting lemma.

**Dyadic cone.** The fields of `DyadicCone` are Mathlib facts: `N` is continuous, `C` is
measurable, `N > 0` on `C` (`fundamentalCone.norm_pos_of_mem`), `C` is stable under positive
scalars (`fundamentalCone.smul_mem_of_mem`), `N (t • x) = |t|^{finrank ℚ K} N x`
(`mixedEmbedding.norm_smul`) and `finrank ℝ V = finrank ℚ K > 0` (`mixedEmbedding.finrank`).

**Coordinate bounds.** Let `R₀` bound the sup norm on the bounded set
`{x ∈ C | N x ≤ 1}` and `R = max R₀ 1`. For `x ∈ C`, put `t = N(x)^{1/n}` and `y = t⁻¹ • x`;
then `y ∈ C`, `N y = 1` and `normAtPlace w x = t * normAtPlace w y`. The upper bound is
`normAtPlace w y ≤ ‖y‖ ≤ R`. For the lower bound, the numbers
`b_v = (normAtPlace v y / R)^{mult v}` lie in `[0, 1]` and their product is
`N(y) / R^{Σ mult v} = R^{-n}` (`sum_mult_eq`); hence
`R^{-n} ≤ b_w ≤ normAtPlace w y / R` (since `mult w ≥ 1`), i.e.
`normAtPlace w y ≥ R^{-n} R`. This gives the bounds with `r = R^{-n} R`.
