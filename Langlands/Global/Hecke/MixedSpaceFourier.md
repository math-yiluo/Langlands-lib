# Fourier analysis on the mixed space

Module `Langlands.Global.Hecke.MixedSpaceFourier`, namespace `Langlands.Global.Hecke`.

This module sets up the archimedean harmonic analysis used in the Tate–Hecke proof of the
global functional equation of Hecke `L`-functions, on the mixed space of a number field. It
combines the one-place computations of `Langlands.Global.Hecke.ArchGaussian` into products over
the infinite places, identifies Mathlib's Fourier transform for a trace-type pairing with Tate's,
and proves the covolume duality `vol(b) vol(b^*) κ² = 1` for a basis and its dual basis by
applying Poisson summation (`Langlands.Global.Hecke.LatticePoissonGeneral`) twice. It is an
internal helper module; it states nothing about `L`-functions or epsilon factors.

## Notation

- `K` is a number field and `V = mixedSpace K = ({w // IsReal w} → ℝ) × ({w // IsComplex w} → ℂ)`,
  Mathlib's mixed space, with componentwise ring structure, the sup norm (`‖x‖` is the maximum
  of the absolute values of all coordinates) and Lebesgue measure `volume` (the product of
  Lebesgue measure on each `ℝ` and the area measure `dx dy` on each `ℂ`). For `x : V`, `x.1 v`
  is the coordinate at a real place `v` and `x.2 v` at a complex place `v`. `x⁻¹` is the
  componentwise inverse (with `0⁻¹ = 0`).
- `N(x) = mixedEmbedding.norm x`, which is `∏_{v real} |x_v| · ∏_{v complex} |x_v|²`
  (`norm_eq_prod_real_complex`).
- Throughout, `aR : {w // IsReal w} → ℝ` and `aC : {w // IsComplex w} → ℂ` are scalars (one per
  real, resp. complex place); the main results assume them all nonzero.
- `𝐞 t = exp (2π i t)` is Mathlib's `Real.fourierChar` (`Circle`-valued, coerced to `ℂ`); complex
  powers are Mathlib's principal-branch `cpow`; `Γ_ℝ` and `Γ_ℂ` are Mathlib's `Gammaℝ`,
  `Gammaℂ`; `realGaussian`, `complexGaussian`, `realCharFun`, `complexCharFun` are the
  functions of `ArchGaussian`:
  `realGaussian b p x = x^p exp (-(π b x²))`, `realCharFun p t x = (x/|x|)^p |x|^t`,
  `complexGaussian b N z = z̄^N exp (-2π b |z|²)` for `N ≥ 0` and `z^{-N} exp (-2π b |z|²)` for
  `N < 0`, `complexCharFun N t z = (z/|z|)^N |z|^{2t}`.
- Mathlib's Fourier transform for a bilinear form `B` on `V` is
  `VectorFourier.fourierIntegral 𝐞 volume B f w = ∫ 𝐞 (-B x w) • f x dx` (a Bochner integral).

## Provenance

Internal. The constructions follow Tate's thesis (J. T. Tate, *Fourier analysis in number fields
and Hecke's zeta-functions*, in Cassels–Fröhlich, *Algebraic Number Theory* (1967), pp. 305–347):
the product test function at the infinite places is the product of the adapted Gaussians of §2.5
(the computations "k Real" and "k Complex", pp. 316–319), and the character `x ↦ 𝐞 (T x)` plays
the role of the archimedean part of Tate's standard additive character built from the local
traces (§2.2 and §4.1), with the sign and scaling conventions of `ArchGaussian`. The scaling
rule `fourierIntegral_comp_mul` is the computation `ĝ(x) = |a|⁻¹ f̂(x/a)` in the proof of Theorem
4.2.1 (Riemann–Roch, p. 333). The covolume duality `measureReal_parallelepiped_mul_dualBasis` is
the finite-dimensional form of Tate's remark closing §4.2 (pp. 333–334): carrying out the
Poisson formula with an unknown measure `μ(D)` of the fundamental domain and iterating it gives
`μ(D)² = 1`. Here the statement is written for an arbitrary real basis `b` of `V`, its dual basis
for the pairing `B(x, y) = -T(xy)`, and Lebesgue measure (which is not self-dual for this
pairing, so the constant `κ` appears); this formulation is internal. All conventions (signs,
Lebesgue measure, the parametrization of the characters) are those of `ArchGaussian`.

## Definitions

- `addTrace aR aC : V →ₗ[ℝ] ℝ`, `T(x) = ∑_{v real} aR v · x_v + ∑_{v complex} 2 Re (aC v · x_v)`.
- `tracePairing aR aC : LinearMap.BilinForm ℝ V`, `B(x, y) = -T(x y)` (product in the ring `V`).
- `mixedGaussian aR aC p N x = ∏_{v real} realGaussian |aR v| (p v) (x_v) ·
  ∏_{v complex} complexGaussian ‖aC v‖ (N v) (x_v)`, for `p : {w // IsReal w} → Fin 2` and
  `N : {w // IsComplex w} → ℤ`; written `F_{p,N}` below.
- `mixedGaussianFTConst aR aC p N = ∏_{v real} (√|aR v|)⁻¹ (i · aR v/|aR v|)^{p v} ·
  ∏_{v complex} (2 ‖aC v‖)⁻¹ (i^{|N v|} (aC v/‖aC v‖)^{N v})`; written `c_{p,N}` below.
- `mixedCharFun p t N u x = ∏_{v real} realCharFun (p v) (t v) (x_v) ·
  ∏_{v complex} complexCharFun (N v) (u v) (x_v)`, for `t : {w // IsReal w} → ℂ`,
  `u : {w // IsComplex w} → ℂ` (that is, `∏ sgn(x_v)^{p_v} |x_v|^{t_v} ∏ (x_v/|x_v|)^{N_v} |x_v|^{2u_v}`).
- `mixedGaussianConst aR aC = κ = ∏_{v real} √|aR v| · ∏_{v complex} 2 ‖aC v‖` (a real number).
- `mixedGaussianReal aR aC x = ∏_{v real} exp (-(π |aR v| x_v²)) · ∏_{v complex} exp (-(2π ‖aC v‖ |x_v|²))`,
  the real-valued plain Gaussian.

## Main results

Elementary facts.

- `fourierChar_sum`: `𝐞 (∑_{i ∈ s} f i) = ∏_{i ∈ s} 𝐞 (f i)` for a finite set `s` and real `f`.
- The imported `Langlands.GodementJacquet.WhittakerTorus.ofReal_prod_cpow` from
  `WhittakerTorusCoordinates`: if `f i ≥ 0` for `i ∈ s`, then `(∏_{i ∈ s} f i)^z = ∏_{i ∈ s} (f i)^z`.
- `ofReal_sq_cpow`: for `r ≥ 0`, `(r²)^z = r^{2z}`.
- `ofReal_inv_cpow_of_nonneg`: for `r ≥ 0`, `(r⁻¹)^z = r^{-z}`.
- `exists_pos_le_of_fintype`: a positive function on a finite type has a positive lower bound.
- `exists_pow_mul_exp_neg_le`: for `k : ℕ` and `b > 0` there is `C > 0` with
  `r^k exp (-(b r²)) ≤ C exp (-(b/2 · r²))` for all `r ≥ 0`.
- `exists_exp_neg_mul_sq_le_rpow`: for `c > 0` and real `r` there is `C > 0` with
  `exp (-(c u²)) ≤ C (1 + u)^{-r}` for all `u ≥ 0`.

One-dimensional Gaussians.

- `norm_realGaussian`: `‖realGaussian b p x‖ = |x|^p exp (-(π b x²))`.
- `norm_complexGaussian`: `‖complexGaussian b N z‖ = |z|^{|N|} exp (-(2π b |z|²))`.
- `continuous_realGaussian`, `continuous_complexGaussian`.
- `integral_realGaussian_mul_fourierChar`: for real `a ≠ 0`, `p : Fin 2` and real `y`,
  `∫ realGaussian |a| p x · 𝐞 (a x y) dx = (√|a|)⁻¹ (i · a/|a|)^p · realGaussian |a| p y`
  (the cases `p = 0, 1` of `ArchGaussian` combined).

The mixed space.

- `norm_eq_prod_real_complex`: `N(x) = (∏_{v real} |x_v|) · ∏_{v complex} |x_v|²`.
- `sq_norm_le_sum`: `‖x‖² ≤ ∑_{v real} x_v² + ∑_{v complex} |x_v|²`.

The trace and the pairing.

- `addTrace_apply`: the defining formula of `T`.
- `fourierChar_addTrace`: `𝐞 (T x) = ∏_{v real} 𝐞 (aR v · x_v) · ∏_{v complex} 𝐞 (2 Re (aC v · x_v))`.
- `tracePairing_apply`: `B(x, y) = -T(x y)`; `tracePairing_comm`: `B(x, y) = B(y, x)`;
  `tracePairing_isSymm` and `tracePairing_flip_isSymm`: `B` and `B.flip` are symmetric.
- `addTrace_mul_conj`: `T(x · x') = ∑_{v real} (aR v · x_v)² + ∑_{v complex} 2 |aC v · x_v|²`, where
  `x'` has coordinates `aR v · x_v` (real `v`) and `conj (aC v · x_v)` (complex `v`).
- `tracePairing_nondegenerate`: if all `aR v` and `aC v` are nonzero, `B` is nondegenerate.
- `fourierIntegral_tracePairing_eq`: Mathlib's Fourier transform for `B` is Tate's,
  `VectorFourier.fourierIntegral 𝐞 volume B f w = ∫ 𝐞 (T (x w)) · f x dx`.
- `fourierIntegral_comp_mul` (scaling): for `y : V` with `N(y) ≠ 0`, the Fourier transform of
  `x ↦ f (y x)` at `w` equals `N(y)⁻¹` times the Fourier transform of `f` at `y⁻¹ w`.

The product Gaussian. Assume all `aR v`, `aC v` nonzero.

- `continuous_mixedGaussian`: `F_{p,N}` is continuous (no hypothesis on `aR`, `aC`).
- `fourierIntegral_mixedGaussian`: the Fourier transform of `F_{p,N}` for `B` at `w` is
  `c_{p,N} · F_{p,-N}(w)`.
- `exists_norm_mixedGaussian_le`: there are `C > 0` and `c > 0` with
  `‖F_{p,N}(x)‖ ≤ C exp (-(c ‖x‖²))` for all `x`.
- `exists_norm_mixedGaussian_le_rpow`: for every real `r` there is `C` with
  `‖F_{p,N}(x)‖ ≤ C (1 + ‖x‖)^{-r}` for all `x` (the decay hypothesis of `LatticePoissonGeneral`).

Characters and zeta integral.

- `realCharFun_inv`: `realCharFun p t (x⁻¹) = realCharFun p (-t) x` (`p : ℕ`, `t : ℂ`, `x : ℝ`).
- `complexCharFun_inv`: `complexCharFun N u (z⁻¹) = complexCharFun (-N) (-u) z`.
- `mixedCharFun_inv`: `mixedCharFun p t N u (x⁻¹) = mixedCharFun p (-t) (-N) (-u) x`.
- `integral_mixedGaussian_mul_mixedCharFun`: if all `aR v`, `aC v` are nonzero,
  `Re (s + t_v + p_v) > 0` for every real `v` and `Re (s + u_v + |N_v|/2) > 0` for every complex `v`,
  then
  `∫ F_{p,N}(x) · mixedCharFun p t N u x · N(x)^{s-1} dx =
   ∏_{v real} |aR v|^{-(s + t_v + p_v)/2} Γ_ℝ(s + t_v + p_v) ·
   ∏_{v complex} (π/2) ‖aC v‖^{-(s + u_v + |N_v|/2)} Γ_ℂ(s + u_v + |N_v|/2)`.

Covolume duality. Assume all `aR v`, `aC v` nonzero.

- `mixedGaussianReal_pos`: `mixedGaussianReal aR aC x > 0`.
- `mixedGaussian_zero_zero`: `F_{0,0}(x) = mixedGaussianReal aR aC x` (as a complex number).
- `mixedGaussianConst_pos`: `κ > 0`.
- `mixedGaussianFTConst_zero_zero`: `c_{0,0} = κ⁻¹`.
- `fourierIntegral_mixedGaussian_zero_zero`: the Fourier transform of `F_{0,0}` for `B` is
  `κ⁻¹ F_{0,0}`.
- `measureReal_parallelepiped_mul_dualBasis`: for any finite index type `ι` and basis
  `b : Basis ι ℝ V`, with `b^* = B.flip.dualBasis _ b` the dual basis for the pairing
  (`B (b i) (b^* j) = δ_{ij}`),
  `vol(parallelepiped b) · vol(parallelepiped b^*) · κ² = 1`, the volumes being the real-valued
  Lebesgue volumes.

## Implemented proof

**Elementary facts.** `fourierChar_sum` is an induction over the finite set using
`AddChar.map_add_eq_mul`. The existing `WhittakerTorus.ofReal_prod_cpow` is reused;
its proof is finite-set induction using `mul_cpow_ofReal_nonneg`. `ofReal_sq_cpow` is trivial for `r = 0`
and is `ofReal_rpow_cpow` with exponent `2` for `r > 0`. `ofReal_inv_cpow_of_nonneg` is
Mathlib's `inv_cpow` (valid as the argument of a nonnegative real is `0 ≠ π`) and `cpow_neg`.
`exists_pos_le_of_fintype` takes the minimum over `Finset.univ` (or `1` if the type is empty).
For `exists_pow_mul_exp_neg_le`, split `exp(-br²) = exp(-br²/2)²`; the bound
`r^k ≤ 1 + r^{2k} ≤ (1 + k!(2/b)^k) exp(br²/2)` follows from `(br²/2)^k/k! ≤ exp(br²/2)`
(`Real.pow_div_factorial_le_exp`), giving `C = 1 + k!(2/b)^k`. For
`exists_exp_neg_mul_sq_le_rpow`, take an integer `k ≥ r`; from
`u² ≥ (1+u)²/2 - 1` one has `exp(-cu²) ≤ e^c exp(-(c/2)(1+u)²)`, the previous lemma with
`b = c/2` bounds `(1+u)^k exp(-(c/2)(1+u)²)` by a constant, and `(1+u)^{-k} ≤ (1+u)^{-r}`.

**Gaussian norms.** Direct from the definitions (`Complex.norm_exp_ofReal`,
`Complex.norm_conj`, and `N.toNat + (-N).toNat = |N|`). The Fourier transform for `p : Fin 2` is
a case split on `p = 0, 1` using `integral_realGaussian_zero_mul_fourierChar` and
`integral_realGaussian_one_mul_fourierChar` from `ArchGaussian`.

**Norm and sup norm.** `norm_eq_prod_real_complex` is `mixedEmbedding.norm_apply` split over real
and complex places (`InfinitePlace.prod_eq_prod_mul_prod`, with multiplicities `1` and `2`).
`sq_norm_le_sum`: each of the two sup norms is bounded by the square root of the corresponding
sum of squares, and `‖x‖` is their maximum.

**Pairing.** `addTrace` is ℝ-linear (the real part of `aC v · (c x_v)` is `c` times that of
`aC v · x_v` for real `c`). `tracePairing` is built with `LinearMap.mk₂` from bilinearity of the
ring product; symmetry is commutativity of `V`. For `addTrace_mul_conj`, `aC z · conj (aC z)` is
`|aC z|²` (`mul_conj`). Nondegeneracy: if `B(x, ·) = 0`, evaluating at the `x'` of
`addTrace_mul_conj` gives a sum of nonnegative terms equal to `0`, so every `aR v · x_v` and
`aC v · x_v` vanishes, hence `x = 0` since the scalars are nonzero
(`Nondegenerate.ofSeparatingLeft`). `fourierIntegral_tracePairing_eq` unfolds the definition:
`-B(x, w) = T(x w)`.

**Scaling.** The change of variables `x ↦ y x` on `V` has Jacobian `N(y)`
(`integral_comp_mul_left` from `MixedSpaceUnfolding`): applied to
`u ↦ 𝐞 (T (u · y⁻¹ w)) f(u)` it gives
`∫ 𝐞 (T (y x · y⁻¹ w)) f(y x) dx = N(y)⁻¹ ∫ 𝐞 (T (u y⁻¹ w)) f(u) du`, and
`y x · y⁻¹ w = x w` because `y y⁻¹ = 1` when `N(y) ≠ 0`
(`mul_inv_cancel_of_norm_ne_zero`).

**Fourier transform of the product Gaussian.** By `fourierChar_addTrace` the integrand
`𝐞 (T (x w)) F_{p,N}(x)` is the product over real places of
`realGaussian |aR v| (p v) (x_v) 𝐞 (aR v · x_v · w_v)` times the product over complex places of
`complexGaussian ‖aC v‖ (N v) (x_v) 𝐞 (2 Re (aC v · x_v · w_v))`. Since `volume` on `V` is the
product measure, `integral_prod_mul` separates the real and complex factors and
`integral_fintype_prod_volume_eq_prod` turns each into a product of one-variable integrals. Each
real integral is `integral_realGaussian_mul_fourierChar` (with `a = aR v`, `y = w_v`), each
complex one is `integral_complexGaussian_mul_fourierChar` of `ArchGaussian` (with `a = aC v`),
and regrouping the products gives `c_{p,N} F_{p,-N}(w)`.

**Decay.** For each place, `exists_pow_mul_exp_neg_le` bounds the one-variable norm
(`norm_realGaussian`, `norm_complexGaussian`) by `C_v exp(-(c x_v²))` (resp. `|x_v|²`), where
`c > 0` is a common lower bound of all `π|aR v|/2` and `π‖aC v‖` (`exists_pos_le_of_fintype`). Multiplying
gives `‖F_{p,N}(x)‖ ≤ (∏ C_v) exp(-c (∑ x_v² + ∑ |x_v|²)) ≤ (∏ C_v) exp(-c ‖x‖²)` by
`sq_norm_le_sum`. Polynomial decay then follows from `exists_exp_neg_mul_sq_le_rpow` at
`u = ‖x‖`.

**Characters.** For `x ≠ 0`, `x⁻¹/|x⁻¹| = x/|x|`, and `|x⁻¹|^t = |x|^{-t}`
(`ofReal_inv_cpow_of_nonneg`); for `x = 0` both sides agree trivially. For complex `z`,
`z⁻¹/|z⁻¹| = (z/|z|)⁻¹`, so `(z⁻¹/|z⁻¹|)^N = (z/|z|)^{-N}` (`inv_zpow'`), and
`|z⁻¹|^{2u} = |z|^{-2u}`. The product version is coordinatewise.

**Zeta integral.** Using `norm_eq_prod_real_complex`, `ofReal_prod_cpow` and
`ofReal_sq_cpow`, `N(x)^{s-1} = ∏_{v real} |x_v|^{s-1} ∏_{v complex} |x_v|^{2(s-1)}`, so the
integrand is a product of one-variable functions; it is separated exactly as for the Fourier
transform (`integral_prod_mul`, `integral_fintype_prod_volume_eq_prod`), and each factor is
`integral_realGaussian_mul_realCharFun` (with `b = |aR v| > 0`) or
`integral_complexGaussian_mul_complexCharFun` (with `b = ‖aC v‖ > 0`) from `ArchGaussian`.

**Covolume duality.** `F_{0,0}` is the real positive function `mixedGaussianReal`, and
`fourierIntegral_mixedGaussian` with `p = 0`, `N = 0` gives `F̂_{0,0} = κ⁻¹ F_{0,0}`
(`c_{0,0} = κ⁻¹` by unfolding). Let `G = F_{0,0}` as an element of `C(V, ℂ)`; it satisfies the
decay hypothesis of `LatticePoissonGeneral` with `r = dim V + 1`
(`exists_norm_mixedGaussian_le_rpow`), and so does `Ĝ = κ⁻¹ G`. For any basis `c`, Poisson
summation `tsum_add_latticeVec_eq` at the point `0` gives
`∑_n G(latticeVec c n) = vol(c)⁻¹ κ⁻¹ ∑_m G(latticeVec c^* m)`, where `latticeVec c n = ∑ n_i c_i`
for `n : ι → ℤ` (the character factor is `𝐞 0 = 1`). Applying this to `b` and to `b^*`, and using
`(b^*)^* = b` (`LinearMap.BilinForm.dualBasis_dualBasis`, since `B.flip` is symmetric), gives
`S = vol(b)⁻¹ κ⁻¹ vol(b^*)⁻¹ κ⁻¹ S` for `S = ∑_n G(latticeVec b n)`. The sum `S` is the image in
`ℂ` of a summable series of positive reals (`summable_add_latticeVec_of_decay`), hence `S ≠ 0`
(`Summable.tsum_pos`). The volumes are positive (`measureReal_parallelepiped_pos`) and `κ > 0`,
so cancelling `S` gives `vol(b) vol(b^*) κ² = 1`.
