# A bound for the theta series in torus coordinates

Module `Langlands.Global.RankinSelberg.EqualAnalyticThetaBound`, namespace
`Langlands.Global.RankinSelbergGlobal.EqualAnalytic`.

**`exists_thetaNorm_le`**: let `Ψ` be dominated (`IsRowDominated`), `Q ⊆ GL_n(𝔸)` compact and
`N > n [F:ℚ]` an integer. There is `K ≥ 0` such that
`Θ⁺(Ψ, A(x) q) ≤ K exp (-N t)` whenever `t ≤ x_j` for all `j` and `q ∈ Q`. Here
`A(x) = diag(e^(x_1), …, e^(x_n))` at every infinite place (`AdelicGL.ofInfinite`, `torInf`).

## Proof

1. `exists_uniform_dominated`: right translates `Ψ(· q)`, `q ∈ Q`, are dominated with uniform
   constants. A common denominator `d` controls the finite coordinates, because the finite
   entries of `q⁻¹` range over a compact set (`exists_integer_mul_mem_of_isCompact`). A common
   bound `(1 + ‖x_∞‖)^N |Ψ(x q)| ≤ K₁` holds, because the archimedean size of `q⁻¹`
   (`invArchSize`) is continuous, hence bounded on `Q`
   (`norm_archimedeanCoordinates_mul_le'`, `pow_mul_le_aux`).
2. For `y = ξ A(x)`: the finite coordinates of `y` are those of `ξ`. So `Ψ(y q) ≠ 0` forces
   `ξ ∈ (d⁻¹𝒪)^n` (`exists_eq_algebraMap_of_integral`). The archimedean coordinates are
   `e^(x_j) ξ_j`, so `‖ξ‖ ≤ e^(-t) ‖y_∞‖`
   (`archimedeanCoordinates_ratRow_mul_torInf`, `finiteCoordinates_ratRow_mul_torInf`).
3. Nonzero lattice points have `‖ξ‖ ≥ δ > 0` (`exists_pos_le_norm_rowEmbedding`). This follows
   from the summability `summable_integralRows` of Part A: only finitely many lattice points
   have norm `≤ 1` (`exists_pos_le_of_summable`).
4. With `a = ‖ξ‖ ≥ δ`: `(1 + ‖y_∞‖)^(-N) ≤ e^(-N t) (1/δ + 1)^N (1 + a)^(-N)` (`real_bound_aux`;
   `norm_rowMul_torInf_le` assembles the pointwise bound). The sum of `(1 + ‖ξ‖)^(-N)` over the
   lattice (`latticeWeight`) is finite (`summable_latticeWeight`).

## Provenance

This is the standard estimate behind the growth of theta series in a Siegel domain. Cogdell
2004 does not spell it out; it is implicit in the convergence statements on printed
pp.209–210. The proof is internal.
