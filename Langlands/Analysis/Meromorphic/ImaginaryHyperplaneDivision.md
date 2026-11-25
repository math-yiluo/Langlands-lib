# Division by real linear forms near the imaginary subspace

Module `Langlands.Analysis.Meromorphic.ImaginaryHyperplaneDivision` proves a
removable-singularity statement in several complex variables: near a point of
the imaginary subspace `iℝⁿ ⊆ ℂⁿ`, a holomorphic function that is bounded on
`iℝⁿ` by a constant times a product of linear forms with real coefficients is
divisible by that product. It was written for the holomorphy and unitarity of
intertwining operators on the imaginary axis
(`Langlands.Global.IntertwiningImaginaryUnitarityStatement`). It imports only
Mathlib. All declarations are in the namespace
`Langlands.Analysis.Meromorphic.ImaginaryHyperplane`. Points of `ℂⁿ` are
functions `Fin n → ℂ` with the sup norm; "imaginary" means `(s t).re = 0` for
all `t`, and `ℝⁿ` sits in `ℂⁿ` as `x ↦ (fun t => (x t : ℂ))`.

## Source

E. Lapid, *On Arthur's asymptotic inner product formula of truncated
Eisenstein series*, Clay Math. Proc. 13 (2011), registered as
`lapid-2011-asymptotic-inner-product-truncated-eisenstein`, pp.328–329 (PDF
pp.337–338): "a meromorphic function `f` on `ℂⁿ` with singularities along
hyperplanes of the form `⟨λ, v − v₀⟩ = 0`, `λ ∈ ℝⁿ`, `v₀ ∈ ℂⁿ`, and whose
restriction to `ℝⁿ` is in `L²(ℝⁿ)`, must be holomorphic near `ℝⁿ`". Lapid
works with `ℝⁿ` and square integrability. Here the real subspace is `iℝⁿ`, as
for the imaginary axis `i𝔞_P^*`, and the hypothesis is a pointwise bound. The
proof below is not Lapid's sketch, which looks at a single hyperplane at a
generic point. It is a Cauchy-integral argument along a real direction,
written for this module (provenance: derived).

## Main theorem

`exists_differentiableOn_mul_eq_of_norm_le_on_imaginary`. Let `ι` be a finite
type and `ℓ k : ℂⁿ →ₗ[ℂ] ℂ` linear forms such that

- `ℓ k` is real on `ℝⁿ`: `(ℓ k x).im = 0` for real `x` (`hreal`);
- `ℓ k` does not vanish on `ℝⁿ`: some real `x` has `ℓ k x ≠ 0` (`hne`).

Let `s₀` be imaginary, `W` an open neighbourhood of `s₀`, `h` complex
differentiable on `W` and `C : ℝ`. Write `L s = ∏ k, ℓ k (s - s₀)`. Assume
`‖h s‖ ≤ C · ‖L s‖` for every imaginary `s ∈ W` with `L s ≠ 0`. Then there are
`δ > 0` and a function `c`, complex differentiable on `ball s₀ δ`, with
`L s · c s = h s` on `ball s₀ δ`.

Repeated factors are allowed (`ι` may index a factor several times), which is
how a power `(∏ β, ⟨λ − λ₀, β^∨⟩)^m` enters in the consumer.

## Proof

1. *A real direction.* `exists_real_forall_ne_zero`: there is a real vector
   `v` with `ℓ k v ≠ 0` for all `k`. Each set `{x | ℓ k x ≠ 0}` is open and
   dense in `ℝⁿ` (move along a real vector on which `ℓ k` does not vanish), so
   their finite intersection is dense by Baire's theorem
   (`dense_iInter_of_isOpen`). Write `V` for `v` in `ℂⁿ` and `a k = ℓ k V`;
   each `a k` is real and nonzero.
2. *Radii.* Choose `R₀` with `ball s₀ R₀ ⊆ W`, put
   `ρ = R₀ / (4(‖V‖ + 1))`, and choose `δ ≤ R₀/4` so small that
   `‖ℓ k (s − s₀)‖ < ρ ‖a k‖` on `ball s₀ δ`. Then for `s ∈ ball s₀ δ` the
   points `s + ζV`, `|ζ| < 2ρ`, lie in `W`, and on the circle `|ζ| = ρ` every
   factor `ℓ k (s − s₀) + ζ a k` of `L (s + ζV)` is nonzero.
3. *The candidate.* With `g = h / L`, holomorphic on the open set
   `O = W ∩ {L ≠ 0}`, set `c s = Real.circleAverage (ζ ↦ g (s + ζ • V)) 0 ρ`,
   the mean of `g` over the circle `s + ρ e^{iθ} V`.
4. *`c` is holomorphic* (`differentiableAt_circleAverage_comp_add`). The
   circle average is `(2π)⁻¹ ∫₀^{2π} g (s + ρ e^{iθ} V) dθ`. Differentiation
   under the integral (`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`)
   needs a uniform bound for `fderiv ℂ g` near the compact tube
   `{s₀ + ρ e^{iθ} V}`. It comes from the Cauchy estimate
   `norm_fderiv_le_of_forall_mem_closedBall_norm_le`
   (`‖fderiv ℂ g y‖ ≤ M / r` when `g` is differentiable and bounded by `M` on
   `closedBall y r`), proved by restricting `g` to the complex lines
   `z ↦ y + z u` and applying the one-variable estimate
   `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`. Measurability of the
   derivative is `measurable_fderiv`. Only the fixed function `g` is
   differentiated, so no regularity of `h` beyond complex differentiability is
   used.
5. *One variable on the imaginary subspace.* For imaginary `s ∈ ball s₀ δ`,
   `φ z = h (s + zV)` is holomorphic on `|z| < 2ρ` and
   `L (s + zV) = ∏ k, (b k + z a k)` with `b k = ℓ k (s − s₀)` imaginary. The
   zeros `−b k / a k` lie on `iℝ`, and on `iℝ` the bound gives
   `‖φ z‖ ≤ C ‖∏ k, (b k + z a k)‖`. `exists_mul_eq_of_bound_on_imaginary`
   divides `φ` by the product. The bound first extends by continuity to the
   zeros of the product on `iℝ` (they are isolated; approach along `z₁ + it`,
   `le_of_eventually_le_along_imaginary`). Then
   `exists_mul_eq_of_bound_on_imaginary_aux` removes one factor at a time:
   the bound forces `φ(z₁) = 0` at a zero `z₁` in the disc, `φ` is
   `(z − z₁)` times its `dslope` (holomorphic by
   `Complex.differentiableOn_dslope`), and the bound passes to the quotient.
   This gives `ψ`, holomorphic on the disc, with `∏ (b k + z a k) · ψ z = φ z`.
6. *The equation on the imaginary subspace.* On the circle `|ζ| = ρ`,
   `g (s + ζV) = ψ ζ`, so `c s = circleAverage ψ 0 ρ = ψ 0` by the mean value
   property `DiffContOnCl.circleAverage`, and
   `L s · c s = ∏ b k · ψ 0 = φ 0 = h s`.
7. *Identity theorem for `iℝⁿ`* (`eqOn_zero_of_eqOn_imaginary`). The function
   `L · c − h` is holomorphic on the convex ball `ball s₀ δ` and vanishes at
   its imaginary points. For `s` in the ball, the complex line
   `γ z = i·Im s + z·Re s` passes through `s` at `z = 1`, meets the ball in a
   convex set containing `0`, and maps a real interval of `iℝ` around `0` into
   imaginary points of the ball. The one-variable identity theorem
   (`AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`) gives
   vanishing at `z = 1`.

## Other declarations

- `re_neg_div_eq_zero`, `add_mul_eq_mul_sub`: the root `−b/a` of `b + z a` is
  imaginary for imaginary `b` and real `a`; factorisation `b + z a = a (z − (−b/a))`.
- `re_apply_eq_zero_of_imaginary`: a complex linear form that is real on `ℝⁿ`
  is imaginary on `iℝⁿ`.

## Scope

The module is pure complex analysis and makes no claim about automorphic forms.
The bound is used only at imaginary points where the product does not vanish.
