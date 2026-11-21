# Joint holomorphy of the real dual unequal-rank integral over a parameter family

Fix `t < r`, a real unit `a`, a second real unit `b` and quotient measure data `D` for `N_(t+1)(ℝ) \ GL(t+1, ℝ)`. The statement `RealUnequalDualFamilyStatement` concerns the published real dual block integral

`Ψ_(r−t−1)(s; ρ(w_(r+1,t+1)) W̃, Ṽ) = ∫ ∫ W̃(rectangularPoint(g, x) · w) Ṽ(g) |det g|^(s − (r−t)/2) dx dg`

(`realUnequalDualIntegral h b D`, with kernel `realUnequalDualKernel` and product measure `realUnequalDualMeasure b D`). Here `W̃` is the Weyl inverse transpose of `W`, `w` is the unfolding Weyl element, and the rectangular measure `dx` is self-dual for the real additive character of `b`. The measure parameter `b` is arbitrary; it need not be related to `a`.

The hypotheses are those of the ordinary statement (`RealUnequalOrdinaryFamily`): an open set `S` in a finite-dimensional complex space `E`, a holomorphic `s : E → ℂ`, and families `W p`, `V p` with

- the left characters of `a` and `−a`,
- continuity on the group,
- pointwise holomorphy on `S`, and
- uniform gauges on `S`.

The conclusion is that there is a threshold `σ` with two properties. On `S ∩ {σ < Re s(p)}` the dual kernel is integrable for the product measure, and `p ↦ Ψ_(r−t−1)(s(p); ρ(w) W̃_p, Ṽ_p)` is holomorphic. The theorem `realUnequalDualFamily` proves this. It is the real counterpart of the published `ComplexUnequalDualFamilyStatement`, and it is internal supporting material for the continuation in the inducing exponents of Jacquet (2009), §8.1.

## Proof

**Characters.**
- `HasLeftCharacter.dual`: the Weyl inverse transpose of a function with the left character of `b` has the character of `−b`.
- `HasLeftCharacter.dualTranslate`: the same holds for `g ↦ W̃(g w)`.
- `dualProduct_unipotent_mul`: multiplying the leading block of a rectangular point on the left by an upper unipotent `u` gives the rectangular point of `u g` with the same `x`. The characters of `−a` and `a` then cancel in the product of the two dual functions.
- `dualKernel_mk` and `continuous_dualKernel`: as a result, the kernel can be evaluated at any representative, and it is continuous on the product of the quotient and the rectangular space. The second fact uses that the product of the open quotient map with the identity is a quotient map.

**Domination.** `dual_halfPlaneDomination` proves the domination hypothesis of the generic theorem `ComplexUnequalFamily.differentiableOn_integral_of_halfPlaneDomination` for any `b`. The uniform gauge of `W` passes to `W̃` (`HasUniformGauge.dual`), then to its translate by the orthogonal unfolding Weyl element (`.translate`). It then gives the rectangular bound `HasUniformGauge.rect`, with growth exponent `N1`. The absolute value of `g ↦ W̃(g w)` is left invariant because of its left character. The gauge of `Ṽ` at decay order 0 has exponent `N2`. Set `A = N1 + N2 + ‖L‖`, where `L` is the logarithm of the modular density from the published Iwasawa disintegration of `D`, and `c = (r−t)/2`. The threshold is `σ = A + 1 + c`. For an upper bound `τ`, choose the decay order

`M = ⌈A + (τ − c) + 1 + 2 N1 ((t+1) + (r−t−1)) + 2 (t+1)(r−t−1)⌉`.

At a toral representative with `T = Re s − c ∈ [A+1, τ − c]`, the bound splits into two factors:

- a toral factor `exp(−M Σ max(y_j,0) + (N1+N2) Σ|y_j| + T Σ y_j)`, which the published `sum_coord_le` (applied with `A`, which contains `‖L‖`) together with `L y ≤ ‖L‖ Σ|y_j|` bounds by `exp(−Σ|y_j| − L y)`;
- a rectangular factor `exp(−(M(t+1)/2 − N1((t+1)+(r−t−1))) log(1 + ‖x‖²))`, which the published `exp_neg_mul_log_le` bounds by `rectDecay x = Π (1 + x_(lp)²)^(−1)`.

The majorant `C1 C2 exp(−Σ|alphaQ q| − L(alphaQ q)) · rectDecay x` is a product of an integrable function on the quotient and an integrable function on the rectangle (`integrable_rectDecay`), so it is integrable for the product measure.

**Conclusion.** For fixed `(q, x)` the kernel is a product of two pointwise holomorphic values and an entire determinant factor. The generic theorem gives integrability and holomorphy of the product integral. On absolute convergence, Fubini (`integral_prod`, `dualIntegral_eq_prod`) identifies the product integral with the published iterated integral. The rectangular measure is σ-finite, and local instances make the quotient σ-compact. Holomorphy then transfers to `realUnequalDualIntegral` by congruence on the half-plane.
