# Unfolding theta integrals over the fundamental cone

Module `Langlands.Global.Hecke.ThetaUnfolding`, namespace `Langlands.Global.Hecke`.

Throughout, `K` is a number field, `V = mixedSpace K` its mixed space with Lebesgue measure,
`ι = mixedEmbedding K : K → V`, `N = mixedEmbedding.norm`, `C = fundamentalCone K` Mathlib's
fundamental cone for the action of the units `(𝓞 K)ˣ` on `V` (`u • x = ι(u) x`), `w =
Units.torsionOrder K` the number of roots of unity, and `θ(a, F)(y) = thetaSeries a F y =
∑'_{γ ∈ K} a(γ) F(ι γ · y)` (from `Langlands.Global.Hecke.ThetaDecay`). A weight `χ : V → ℂ` is
called multiplicative below if `χ(x y) = χ(x) χ(y)` whenever `N(x) ≠ 0 ≠ N(y)`, and `χ(1) = 1`.

The module computes the Mellin integrals over the fundamental cone of theta series with
unit-equivariant coefficients, by unfolding the sum over `Kˣ` into orbits of the units. It is the
"unfolding" step of the Tate–Hecke proof of the functional equation of Hecke `L`-functions, in
the form needed by the internal assembly: the result is a Dirichlet-type sum over orbit
representatives times an archimedean zeta integral over `V`. It states nothing about
`L`-functions.

## Provenance

Internal helper for the proof of the published actual Hecke global functional equation
statement. The computation is the classical unfolding of Hecke's theta-integral representation of
`L`-functions; in idelic form it corresponds to Tate's description of a fundamental domain for
the norm-one ideles modulo `k*` by means of the units (J. T. Tate, *Fourier analysis in number
fields and Hecke's zeta-functions*, in Cassels–Fröhlich, *Algebraic Number Theory* (1967), §4.3
"Multiplicative Theory", pp. 334 ff.). Here it is carried out on
the mixed space with Mathlib's fundamental cone, using the unit unfolding
`hasSum_setIntegral_unit_smul` of `Langlands.Global.Hecke.MixedSpaceUnfolding`; the abstract
indexing of the orbits by `P × (𝓞 K)ˣ ≃ Kˣ` and the exact hypotheses are chosen for the internal
assembly.

## Definitions

- `unfoldIntegrand a F χ s γ y = a(γ) F(ι γ · y) χ(y) N(y)^(s-1)` (complex power of the real
  number `N(y)`).
- An instance `Countable Kˣ`, from the injectivity of `Units.val` and `Countable K`.

## Main results

### Changes of variables

- `integrable_comp_mul_left_iff`: if `N(y) ≠ 0`, `x ↦ f(y x)` is integrable iff `f` is.
- `norm_mixedEmbedding_units_ne_zero`, `norm_mixedEmbedding_units_pos`: `N(ι γ) > 0` for
  `γ ∈ Kˣ`.
- `mixedSpace_inv_zero`: `0⁻¹ = 0` in `V` (componentwise inverse).
- `mixedEmbedding_inv`: `ι(μ⁻¹) = (ι μ)⁻¹` for all `μ ∈ K`.
- `coe_units_inv`: the image in `K` of `u⁻¹` is the inverse of the image of `u`, for
  `u ∈ (𝓞 K)ˣ`.
- `integrable_comp_inv_iff`: `x ↦ N(x)⁻² g(x⁻¹)` is integrable iff `g` is.
- `integral_inv_eq_and_integrable`: `y ↦ G(y⁻¹) χ(y) N(y)^(-s-1)` is integrable iff
  `y ↦ G(y) χ(y⁻¹) N(y)^(s-1)` is, and their integrals agree.

### Unfolding

The following assume `χ` multiplicative.

- `ne_zero_of_multiplicative`: `χ(c) ≠ 0` when `N(c) ≠ 0`.
- `unfoldIntegrand_eq`: for `γ ∈ Kˣ`, `c = ι γ` and `N(y) ≠ 0`,
  `unfoldIntegrand a F χ s γ y = a(γ) χ(c)⁻¹ N(c)^(1-s) · F(c y) χ(c y) N(c y)^(s-1)`.
- `integrable_unfoldIntegrand`: if `F χ N^(s-1)` is integrable, so is each
  `unfoldIntegrand a F χ s γ`, `γ ∈ Kˣ`.
- `integral_unfoldIntegrand`: `∫ unfoldIntegrand a F χ s γ = a(γ) χ(ι γ)⁻¹ N(ι γ)^(-s)
  ∫ F χ N^(s-1)`.
- `integral_norm_unfoldIntegrand`: `∫ ‖unfoldIntegrand a F χ s γ‖ = |a(γ)| |χ(ι γ)|⁻¹
  N(ι γ)^(-Re s) ∫ ‖F χ N^(s-1)‖`.
- `unfoldIntegrand_units_mul`: if `a(u γ) = χ(ι u) a(γ)` for units `u`, then for `N(x) ≠ 0`,
  `unfoldIntegrand a F χ s (u γ) x = unfoldIntegrand a F χ s γ (u • x)`.
- `integral_thetaSeries_unfold_of_summable`: let `gen : P → Kˣ` and `e : P × (𝓞 K)ˣ ≃ Kˣ` with
  `e(p, u) = u · gen p` (representatives of the orbits of the units), `a(u γ) = χ(ι u) a(γ)`,
  `γ ↦ a(γ) F(ι γ · x)` summable over `K` at every `x ∈ C`,
  `∑_p |a(gen p)| |χ(ι gen p)|⁻¹ N(ι gen p)^(-Re s)` summable and `F χ N^(s-1)` integrable. Then

  `∫_C (θ(a, F)(x) - a(0) F(0)) χ(x) N(x)^(s-1) dx =
   w ∑_p a(gen p) χ(ι gen p)⁻¹ N(ι gen p)^(-s) ∫_V F χ N^(s-1)`.
- `integral_thetaSeries_unfold`: the same with the pointwise summability replaced by: `a` bounded
  and supported in a fractional ideal, `|F(z)| ≤ C e^{-c ‖z‖²}` with `c > 0`.
- `integral_thetaSeries_inv_unfold` (dual integral): with `b(u μ) = χ(ι u)⁻¹ b(μ)`, `b` bounded and
  supported in a fractional ideal, `G` with Gaussian decay,
  `∑_p |b(gen p⁻¹)| |χ(ι gen p)|⁻¹ N(ι gen p)^(Re s)` summable and `G(y⁻¹) χ(y) N(y)^(-s-1)`
  integrable,

  `∫_C (θ(b, G)(x⁻¹) - b(0) G(0)) χ(x) N(x)^(-s-1) dx =
   w ∑_p b(gen p⁻¹) χ(ι gen p)⁻¹ N(ι gen p)^s ∫_V G(y⁻¹) χ(y) N(y)^(-s-1) dy`.

## Proofs

**Changes of variables.** Multiplication by `y` pushes Lebesgue measure to `N(y)⁻¹` times
itself (`map_mulHomeomorph_volume` of `MixedSpaceUnfolding`), and integrability is invariant
under such a positive multiple (`integrable_map_equiv`, `integrable_smul_measure`). For the
inversion, `x ↦ x⁻¹` is a bijection of the conull open set `{N ≠ 0}` with derivative
multiplication by `-x⁻²`, whose determinant has absolute value `N(x)⁻²` (as in the proof of
`integral_comp_inv` of `MixedSpaceUnfolding`); Mathlib's
`integrableOn_image_iff_integrableOn_abs_det_fderiv_smul` gives `integrable_comp_inv_iff`. For
`integral_inv_eq_and_integrable`, apply `integrable_comp_inv_iff` and `integral_comp_inv` to
`g(y) = G(y⁻¹) χ(y) N(y)^(-s-1)`: for `N(x) ≠ 0`,
`N(x)⁻² g(x⁻¹) = G(x) χ(x⁻¹) N(x)^(s+1) N(x)⁻² = G(x) χ(x⁻¹) N(x)^(s-1)`. `ι(μ⁻¹) = (ι μ)⁻¹`
holds since `ι μ · ι(μ⁻¹) = 1` in the commutative monoid `V` with componentwise inverses (and
both sides vanish for `μ = 0`).

**Pointwise identities.** Multiplicativity gives `χ(y) = χ(c)⁻¹ χ(c y)` and
`N(y)^(s-1) = N(c)^(1-s) N(c y)^(s-1)` (`N` is multiplicative and `N(c) > 0`), which is
`unfoldIntegrand_eq`. Then `∫ unfoldIntegrand = a(γ) χ(c)⁻¹ N(c)^(1-s) ∫ (F χ N^(s-1))(c y) dy
= a(γ) χ(c)⁻¹ N(c)^(1-s) N(c)⁻¹ ∫ F χ N^(s-1)` by `integral_comp_mul_left`, and the same with
norms (`|N(c)^(1-s)| = N(c)^(1-Re s)`). For `unfoldIntegrand_units_mul`,
`ι(u γ) x = ι γ (ι u x)`, `χ(ι u x) = χ(ι u) χ(x)` and `N(ι u x) = N(x)` (`norm_unit`).

**Unfolding.** At `x ∈ C` (where `N(x) > 0`) the series `θ(a, F)(x)` converges, so
`θ(a, F)(x) - a(0) F(0) = ∑_{γ ∈ Kˣ} a(γ) F(ι γ x)` (`Summable.tsum_eq_add_tsum_ite` and
reindexing along `Units.val`), and the integrand is `∑_{γ ∈ Kˣ} unfoldIntegrand a F χ s γ x`. For
fixed `p`, by `unfoldIntegrand_units_mul` and `he`, `unfoldIntegrand a F χ s (e(p, u)) x =
unfoldIntegrand a F χ s (gen p) (u • x)` on `C`, so the unit unfolding
`hasSum_setIntegral_unit_smul` gives
`∑_u ∫_C unfoldIntegrand (e(p, u)) = w ∫_V unfoldIntegrand (gen p)`, and the same for the norms.
By `integral_norm_unfoldIntegrand` the totals of the norms are
`w |a(gen p)| |χ(gen p)|⁻¹ N(gen p)^(-Re s) ∫ ‖F χ N^(s-1)‖`, summable over `p` by hypothesis;
`summable_prod_of_nonneg` and the bijection `e` show that `γ ↦ ∫_C ‖unfoldIntegrand γ‖` is
summable over `Kˣ`. Hence the sum and the integral over `C` can be interchanged
(`hasSum_integral_of_summable_integral_norm`), and `HasSum.prod_fiberwise` along `e` sums the
result over the orbits; `integral_unfoldIntegrand` evaluates each orbit term.
`integral_thetaSeries_unfold` obtains the pointwise summability from `exists_thetaSeries_decay`
(`ThetaDecay`) and the positive lower bound of the coordinates of `x`
(`exists_pos_le_normAtPlace` of `AdelicPoisson`).

**Dual integral.** Put `a'(γ) = b(γ⁻¹)` and `F'(y) = G(y⁻¹)`. Reindexing `K` by `γ ↦ γ⁻¹` and
`(ι γ x)⁻¹ = ι(γ⁻¹) x⁻¹` show `θ(a', F')(x) = θ(b, G)(x⁻¹)`, and `a'(0) F'(0) = b(0) G(0)`. Since
`χ(ι u⁻¹) = χ(ι u)⁻¹`, `a'(u γ) = b(u⁻¹ γ⁻¹) = χ(ι u) a'(γ)`; the pointwise summability at
`x ∈ C` comes from the decay of `θ(b, G)` at `x⁻¹`. The primal theorem with `-s` in place of `s`
is the claim (`a'(gen p) = b(gen p⁻¹)`).
