# The real unequal-rank integrals along holomorphic families of regular Whittaker functions

Fix `t < r`, a real unit `a`, a second real unit `b` (the self-dual measure parameter of the rectangular variable in the dual integral) and quotient measure data `D` for `N_(t+1)(ℝ) \ GL(t+1, ℝ)`. This module has two statements about the published real unequal-rank integrals `realUnequalIntegral h D W V s` and `realUnequalDualIntegral h b D W V s`, with integrands `realUnequalIntegrand` and `realUnequalDualKernel`.

## The generic regular family

`RealUnequalRegularFamilyBoundsStatement` takes the following data:

- a family `W : (Fin m → ℂ) → GL(r+1, ℝ) → ℂ`, where every iterated right derivative of every `W z` lies in the published regular space `regularFunctions r a`;
- the published locally uniform polynomial growth of all derivatives on all of `ℂ^m` (`RealGodement.HasLocallyUniformDerivativeGrowth univ W`);
- holomorphy of `z ↦ W z g` for every group element `g`;
- a holomorphic map `p : ℂ → ℂ^m`;
- a fixed `V : GL(t+1, ℝ) → ℂ`, where every iterated right derivative lies in `regularFunctions t (−a)`, and these derivatives have polynomial growth in the real matrix height with one common exponent.

The statement says that for every radius `R` there is a threshold `σ` with four properties:

1. For `z` in the open disk `|z| < R` and `Re s > σ`, both the ordinary integrand of `(W (p z), V, s)` and the dual kernel are integrable.
2. `(z, s) ↦ realUnequalIntegral h D (W (p z)) V s` is jointly holomorphic on `ball 0 R × {σ < Re s}`.
3. The dual integral `(z, s) ↦ realUnequalDualIntegral h b D (W (p z)) V s` is also jointly holomorphic there.
4. For every closed vertical strip `x ≤ Re s ≤ y` with `σ < x`, one constant bounds the absolute values of both integrals for all `z` in the disk and all `s` in the strip.

`realUnequalRegularFamilyBounds` proves this.

The two parameters `a` and `b` are independent: the measure parameter `b` need not be related to `a`.

## The canonical Jacquet family

`RealUnequalCanonicalFamilyBoundsStatement` specializes the generic statement to the published real canonical Jacquet map. Fix a parity list `pr : Fin (r+1) → Fin 2`, a compact profile `φ` on the orthogonal group (`IsCompactProfile pr φ`) and a holomorphic `p : ℂ → ℂ^(r+1)` of inducing exponents. Put

`W z = RealGodement.canonicalJacquetMap (−a) pr (p z) (standardSection (p z) φ)`,

the canonical continued Jacquet value of the standard section with compact restriction `φ`. The canonical map for `−a` produces functions with the left character of `a`. For a fixed `V` as above, the conclusion is the same four properties with `W (p z)` replaced by `W z`. `realUnequalCanonicalFamilyBounds` proves it.

This is a derived analytic step, internal to the project, toward continuation in the inducing exponents out of the convergence chamber. It is the real counterpart of the published `ComplexUnequalCanonicalFamilyBoundsStatement`. The reference is Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §8.1.

## Proof

**Reparametrization.** `HasUniformGauge.comp` shows that a uniform gauge on a set `S` passes to `u ↦ W (f u)` on a set `T` when `f` maps `T` into `S`. The constants are unchanged.

**Generic family.** Work on the parameter space `ℂ × ℂ` with the open set `T = ball 0 R × ℂ`, the spectral map `Prod.snd`, the larger family `F (z, s) = W (p z)` and the constant smaller family `B (z, s) = V`.

- The left characters `a` and `−a` and continuity come from the regular spaces (the empty derivative list).
- Pointwise holomorphy of `F` on `T` is the holomorphy of `W · g` composed with `p` and the first projection. `B` is constant.
- The image `p(closedBall 0 R)` is compact. `exists_uniform_derivativeGrowth` turns the locally uniform growth into one exponent and one constant per derivative over this image. `hasUniformGauge_of_derivativeGrowth` then gives a uniform gauge for `W` on the image. `HasUniformGauge.comp` transfers it to `F` on `T`.
- `RealWhittakerGauge.exists_gauge_bound` gives a gauge for `V`, and `hasUniformGauge_const` makes it uniform for `B`.

The theorems `realUnequalOrdinaryFamily` and `realUnequalDualFamily` (with this `b`) then give thresholds `σ` and `τ` for integrability and joint holomorphy. `ordinary_halfPlaneDomination` and `dual_halfPlaneDomination` give thresholds `σ₀` and `τ₀` and, for each upper bound `y`, integrable majorants `M` and `Md` that dominate the integrands at all `(z, s) ∈ T` with `σ₀ < Re s ≤ y` (respectively `τ₀`). The common threshold is `S₀ = max(max σ τ, max σ₀ τ₀)`. Integrability and holomorphy restrict from the larger sets.

For the strip bound, take `C = ∫ ‖M‖ dD.measure` and `Cd = ∫ ‖Md‖` over the dual product measure, and use `max C Cd`. The ordinary integral is bounded by `norm_integral_le_of_norm_le`. For the dual integral, `dualIntegral_eq_prod` (Fubini, under absolute convergence) first rewrites the iterated integral as the integral of the kernel over the product measure, and then the same estimate applies.

**Canonical family.** The published `canonicalJacquetFamily_properties (−a) hφ` gives the following for the published family `canonicalJacquetFamily (−a) hφ` on `ℂ^(r+1)`:

- all derivatives lie in `regularFunctions r (−(−a))`, which `neg_neg` rewrites to `regularFunctions r a`;
- locally uniform derivative growth on all of `ℂ^(r+1)`;
- holomorphy of every derivative at every group element, used here for the empty derivative list.

The generic statement with `m = r + 1` applies. Finally, `canonicalJacquetMap_standardSection` identifies `canonicalJacquetMap (−a) pr (p z)` at the standard section of `φ` with `canonicalJacquetFamily (−a) hφ (p z)`. Rewriting `W` by this function equality gives the canonical statement.
