# Absolute convergence of the corank-one integrals against `W(x; ψ̄)`

Author: Worker 5220. Internal helper module for the proof of
`Langlands.Conductor.SphericalCorankOneConvergenceStatement`; it introduces no
statement. Its main theorem is the clause on convergence (the second conjunct of
that statement and of `SphericalLFactorGenerationStatement`).

## Main theorem

`corankOneConverges_inverseSphericalWhittaker h π hπ ℓ w x`: under Jacquet's
normalizations `h : IsJacquetNormalization q ψ abv ϖ μ`, for an **admissible** `π` of
`GL_(n+2)(F)` (any nonarchimedean local field `F`), any standard functional `ℓ`, any
`w` in `coefficientModel π ℓ` and any `x : Fin (n+1) → ℂˣ`, there is `a : ℝ` with
`CorankOneConverges ψ abv μ w.val (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s`
whenever `a < Re s`. Irreducibility is not used.

## Proof

1. `model_corankOne_torus_bound`: there are `b`, `C`, `A` such that
   `w(diag(ϖ^λ k, 1))` vanishes unless `b ≤ λ_last` (the published
   `model_corankOne_last_exponent_lower_bound`) and is at most `C A^(∑ |λ_i|)` for
   antitone `λ` and `k ∈ GL_(n+1)(O)`. With `c = min(λ_last, 0)`,
   `diag(ϖ^λ k, 1) = ϖ^(λ, c) · diag(k, 1) · ϖ^(0, …, 0, -c)` (`rankInclusion_torus_succ`,
   `torus_snoc_split`, `torus_last_commute`), `(λ, c)` is antitone (`antitone_snoc`),
   and the vectors `π(diag(k,1)) π(ϖ^(0,…,0,-c)) v` for `b ≤ c ≤ 0` form a finite
   set fixed by one principal level (finite orbits under `GL_(n+2)(O)`,
   `Compact.finite_orbit_of_smooth`; normality, `conj_mem_rankPrincipalLevel`).
   Then `whittaker_torus_bound_finite` applies.
2. `corankOneIntegrand_torus_mul`: on `ϖ^λ k` the integrand is
   `w(diag(ϖ^λ k, 1)) · W_x(ϖ^λ) · (q^(-(s-1/2)))^(∑ λ_i)` (right
   `GL_(n+1)(O)`-invariance of `W_x` and of the determinant weight,
   `sphericalWhittaker_torus`, `determinantWeight_eq_degree_power`).
3. `corankOneIntegrand_model_continuous`: the integrand is locally constant on the
   quotient (`isLocallyConstant_of_right_integral`,
   `isLocallyConstant_quotient_of_pullback`), hence continuous and measurable.
4. On the cell of `λ` the integrand is bounded by
   `E λ = Cw Aw^S (Cx Bx^S) r^(∑ λ_i)` if `λ` is antitone with `b ≤ λ_last`, and by
   `0` otherwise (`S = ∑ |λ_i|`, `r = q^(-(Re s - 1/2))`, Schur bound from
   `exists_satakeSchur_bound`). With `exists_sphericalCell_measure_le`, the cell
   integral of `‖f‖` is at most `E λ · μ(cell 0) c^S`.
5. For such `λ` every `λ_i ≥ b`, so the bound is at most a constant times
   `∏_i G(λ_i)` with `G(z) = D^|z| r^z` for `z ≥ b` and `0` otherwise
   (`D = Aw Bx c`). `G` is dominated by a one-sided geometric series
   (`summable_shifted_geometric`) once `D r < 1`, i.e. for
   `Re s > 1/2 + log_q D`; products of summable functions are summable on
   `Fin (n+1) → ℤ` (`summable_prod_fin`).
6. Mathlib's `integrableOn_iUnion_of_summable_integral_norm` over the cells, which
   cover the quotient, gives integrability.

Auxiliary: `prod_real_zpow_eq`, `IsJacquetNormalization.one_lt_q`, `sum_natAbs_snoc`.

## Provenance

JPSS 1983 (H. Jacquet, I. I. Piatetski-Shapiro, J. A. Shalika, *Rankin–Selberg
convolutions*, Amer. J. Math. 105 (1983), 367–464, literature ID
`jpss-1983-rankin-selberg`), Theorem (2.7) (absolute convergence on a right
half-plane), recalled in Jacquet 2012 (literature ID
`jacquet-2012-conductor-correction`), section 1. The proof here is elementary and
works over every nonarchimedean local field.

The residue-cardinality bound is reused from
[EssentialConductorAssembly](EssentialConductorAssembly.md).

The successor-rank lemma `rankInclusion_torus_succ` retains its original
`Fin (n + 1)` parameter. The general-rank `rankInclusion_torus` remains in
[ConductorMinimalityReduction](ConductorMinimalityReduction.md).
