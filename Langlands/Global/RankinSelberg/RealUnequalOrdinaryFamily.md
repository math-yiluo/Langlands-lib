# Joint holomorphy of the real ordinary unequal-rank integral over a parameter family

Fix `t < r`, a real unit `a` and quotient measure data `D` for the left quotient `N_(t+1)(ℝ) \ GL(t+1, ℝ)`. The statement `RealUnequalOrdinaryFamilyStatement` concerns the published real ordinary integral

`Ψ(s; W, V) = ∫ W(diag(g, 1)) V(g) |det g|^(s − (r−t)/2) dg`

(`realUnequalIntegral`, with integrand `realUnequalIntegrand`). Let `E` be a finite-dimensional complex vector space, `S ⊆ E` open, and `s : E → ℂ` holomorphic. Suppose the families `W p` on `GL(r+1, ℝ)` and `V p` on `GL(t+1, ℝ)` satisfy the following, where the holomorphy is only asked on `S`:

- `W p` has the left character of `a` and `V p` that of `−a`, for every `p`;
- each `W p` and `V p` is continuous on the group;
- `p ↦ W p g` and `p ↦ V p g` are holomorphic on `S` for every fixed `g`;
- both families have uniform gauges on `S` (`HasUniformGauge`, from `RealUnequalFamilyGauge`).

Then there is a threshold `σ` with two properties. On `S ∩ {σ < Re s(p)}` the integrand of `Ψ(s(p); W p, V p)` is integrable, and `p ↦ Ψ(s(p); W p, V p)` is holomorphic. The theorem `realUnequalOrdinaryFamily` proves this. It is the real counterpart of the published `ComplexUnequalOrdinaryFamilyStatement`, and it is internal supporting material for the continuation in the inducing exponents of Jacquet (2009), §8.1.

## Proof

`product_unipotent_mul`: padding an upper unipotent matrix of `GL(t+1)` gives an upper unipotent matrix of `GL(r+1)` with the same character value. So the characters of `a` and `−a` cancel in the product `W(diag(g,1)) V(g)`. The determinant factor is also left invariant, so the integrand on the quotient can be evaluated at any representative (`integrand_mk`). It is continuous because the quotient map is open (`continuous_integrand`).

`ordinary_halfPlaneDomination` proves the domination hypothesis of the published generic theorem `ComplexUnequalFamily.differentiableOn_integral_of_halfPlaneDomination`. The published Iwasawa disintegration of `D` gives a constant `κ` and a linear form `L` on `ℝ^(t+1)`, the logarithm of the modular density. Take the padded uniform gauge of `W` with growth exponent `N1`, and the uniform gauge of `V` at decay order 0 with exponent `N2`. Set `A = N1 + N2 + ‖L‖` and `c = (r−t)/2`. The threshold is `σ = (A+1)(t+1) + c`. Given an upper bound `τ`, take the decay order `M = ⌈(A+1)(t+1) + (τ − c)(t+1)⌉`. At a toral representative `torus y · k` with `T = Re s − c` in `[(A+1)(t+1), τ − c]`, the kernel is at most

`C1 C2 · exp(−M rootPos y + (N1+N2) Σ|y_j| + T Σ y_j − M max(y_last, 0))`.

The published exponent estimate `RealConvergenceAnalysis.exponent_le`, applied with `A` (which contains `‖L‖`) and combined with `L y ≤ ‖L‖ Σ|y_j|` (`linear_le`), bounds this by `C1 C2 · exp(−Σ|y_j| − L y)`. The bound depends only on the Iwasawa logarithms `alphaQ q` of the quotient point. It is integrable for `D.measure` by `RealUnequalDualConvergence.integrable_exp_comp_alphaQ`, because its exponent `E(y) = −Σ|y_j| − L y` is continuous and satisfies `L y + E(y) ≤ −Σ|y_j|`.

For fixed `q`, the integrand is a product of the two pointwise holomorphic functions at a chosen representative and the entire factor `exp((s(p) − c) log|det|)`. The generic theorem then gives integrability and holomorphy on `S ∩ {σ < Re s}`.
