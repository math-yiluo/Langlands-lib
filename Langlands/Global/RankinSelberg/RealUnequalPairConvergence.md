# Convergence and holomorphy of both real unequal-rank Rankin–Selberg integrals

Module of an intermediate result of Task 7400, used by the reduction in
`RealUniformContinuationReduction`, towards
`Langlands.Global.RankinSelbergGlobal.RealPlaceFunctionalEquationStatement`. Authored by
Worker 823. Every declaration is proved, with no axioms beyond Lean's standard ones
(`propext`, `Classical.choice`, `Quot.sound`).

Let `t < r`, `n = r + 1`, `m = t + 1`. The unequal-rank functional equation at a real place
compares two integrals:
- `Ψ(s; W, W')` (`ArchimedeanLocal.realUnequalIntegral h D W W'`), an integral over
  `N_m \ GL_m(ℝ)` with integrand `realUnequalIntegrand h W W' s`;
- the dual block integral `Ψ_(n−m−1)(s; ρ(w_(n,m)) W̃, W̃')`
  (`ArchimedeanLocal.realUnequalDualIntegral h a D W W'`). Its kernel
  `realUnequalDualKernel h W W' s` lives on the product of the quotient and the space of real
  `(n − m − 1) × m` matrices, with the measure `realUnequalDualMeasure a D`: the quotient
  measure times the rectangular measure self-dual for `realScaledCharacter a`. Here
  `W̃ = ArchimedeanLocal.dualFunction (r + 1) W`, `W̃' = ArchimedeanLocal.dualFunction (t + 1) W'`
  and `ρ(w_(n,m))` is right translation by `ArchimedeanLocal.unfoldingWeyl h`.

The Library's package `RealJacquet.UnequalEquation h a D W W' …` (module
`RealJacquetConventionReduction`) begins with four conjuncts: both kernels are integrable for
`Re s > σ`, and both integrals are holomorphic there. This module proves these four conjuncts
with one `σ`.

## The statement

`Langlands.Global.RankinSelbergGlobal.RealUnequalPairConvergenceStatement : Prop` says the
following. Let `r, t : ℕ` with `h : t < r`, `D : RealQuotientMeasureData t`, `a : ℝˣ`,
`W : GL_(r+1)(ℝ) → ℂ` and `W' : GL_(t+1)(ℝ) → ℂ`. Assume:
- every iterated right derivative of `W` lies in `RealLocalWhittaker.regularFunctions r a`;
- for some `N`, every iterated right derivative of `W` is bounded by
  `C · realMatrixHeight(g)^N`, where `C` may depend on the derivative but `N` may not;
- every iterated right derivative of `W'` lies in
  `RealLocalWhittaker.regularFunctions t (−a)`;
- the same common-exponent growth bound holds for `W'`.

Then there is `σ` such that, for every `s` with `σ < Re s`:
1. `realUnequalIntegrand h W W' s` is integrable for `D.measure`;
2. `realUnequalDualKernel h W W' s` is integrable for `realUnequalDualMeasure a D`;

and furthermore:

3. `realUnequalIntegral h D W W'` is complex differentiable on `{s : σ < Re s}`;
4. `realUnequalDualIntegral h a D W W'` is complex differentiable on `{s : σ < Re s}`.

The theorem `Langlands.Global.RankinSelbergGlobal.realUnequalPairConvergence` proves it. The
hypotheses are those of `RealUnequalConvergenceStatement` (module `RealUnequalConvergence`).

## Proof structure

The declarations below are in the namespace
`Langlands.Global.RankinSelbergGlobal.RealUnequalPairConvergence`.

### Orthogonality of `w_(n,m)` and the gauge

- `weylLong_mem_unitary'`: the long Weyl element of every size is orthogonal, since it equals
  its inverse transpose and squares to `1`.
- `reindex_mem_unitary`, `blockSum_mem_unitary`: reindexing and block sums preserve
  orthogonality.
- `unfoldingWeyl_mem_unitary`: `w_(n,m) = diag(1_m, w_(n−m))` (reindexed) is orthogonal.
- `hasGauge_translate`: right translation by an orthogonal matrix preserves `HasGauge`.

### Characters

- `realWhittakerCharacter_reflected`: for upper unipotent `u`, the character for `a` at the
  Library's `Whittaker.reflectedUnipotent u` (that is, `w ᵗu⁻¹ w`) equals the character for `−a`
  at `u`, by the Library's `reflectedUnipotent_sum`.
- `norm_realWhittakerCharacter`: the character values have norm `1`.

### Block multiplication

- `index_cases`: every index of `Fin (a + d + 1)` lies in the first, middle or last block.
- `rect_mul`: `rect(u g, x) = rect(u, 0) · rect(g, x)`, entry by entry.
- `rect_zero_apply`, `rectangularPoint_zero`: `rectangularPoint h u 0` is the padded matrix
  `padGL u = diag(u, 1)` of `GL_n(ℝ)`.
- `rectangularPoint_mul`: `rectangularPoint h (u g) x = diag(u, 1) · rectangularPoint h g x`.

### The theorem for uniformly regular functions

`exists_pair_convergence_of_regular` proves the four conclusions under the hypotheses of the
statement:
- `RealUnequalConvergence.exists_convergence_of_regular` gives `σ1` for conclusions 1 and 3.
- Put `V = ρ(w_(n,m)) W̃` and `V' = W̃'`. Both are continuous. By the Library's
  `weylInverseTranspose_left_unipotent` and the character law of `W`,
  `V(u g) = ψ_(−a)(u) V(g)` for upper unipotent `u` of `GL_n(ℝ)`, so `‖V(u g)‖ = ‖V(g)‖`.
  Likewise `V'(u g) = ψ_a(u) V'(g)` for upper unipotent `u` of `GL_m(ℝ)`.
- `HasGauge V` follows from `RealWhittakerGauge.exists_gauge_bound`,
  `RealEqualDualConvergence.hasGauge_dual` and `hasGauge_translate`. `HasGauge V'` follows from
  the first two.
- The kernel `V(rect(g, x)) V'(g)` is invariant under `g ↦ u g`: by `rectangularPoint_mul`,
  `rectangularPoint_zero` and `RealUnequalConvergence.realWhittakerCharacter_padGL`, it is
  multiplied by `ψ_(−a)(u) ψ_a(u) = 1`.
- `RealUnequalDualConvergence.exists_dual_convergence`, with the self-dual measure
  `realSelfDualMeasure a`, gives `σ2` for conclusions 2 and 4. Take `σ = max(σ1, σ2)`.

`realUnequalPairConvergence : RealUnequalPairConvergenceStatement` is
`exists_pair_convergence_of_regular`.

## Relation to the literature

This is the real case of Jacquet, *Archimedean Rankin–Selberg integrals* (2009), Theorem 2.1(i)
(p. 6), for the two integrals compared by the unequal-rank functional equation in
Theorem 2.1(iii): `Ψ(s; W, W')` of (2.4) and `Ψ_j(s; ρ(w_(n,n')) W̃, W̃')` of (2.5) with
`j = n − n' − 1`. Holomorphy in the region of convergence is added. Jacquet proves the
convergence in §5.1 (p. 32) and §5.2 (pp. 33–35). Jacquet's hypothesis that `W` and `W'` are
Whittaker functions of induced representations is replaced by the explicit regularity and
common-exponent growth hypotheses, which are the properties the proof uses (his Lemma 3.7,
p. 15). For the dual side, Jacquet's majorization of `W̃` (p. 17) uses the twisted
representation `g ↦ π(ᵗg⁻¹)` with the linear form `λ ∘ π(w_n)`, a `ψ̄`-form when `λ` is a
`ψ`-form. Here the gauge estimate of `W̃` is derived at the level of functions in
`RealEqualDualConvergence`, and the character of `W̃` is computed from
`reflectedUnipotent_sum`. The abscissa `σ` is only shown to exist.
