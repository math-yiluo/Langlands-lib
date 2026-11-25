# Derivatives of weighted polynomials

Let `T_j` (`j` in a finite type `κ`) be functions of degree `≤ e` (`degLE ι e`) taking positive
real values (`IsPosReal`), `σ_j ∈ ℂ`, `ω = ∏_j T_j^{σ_j}` (complex powers) and `D = ∏_j T_j`.

- `IsPosReal T`: every value of `T` is a positive real; `IsPosReal.ne_zero`,
  `IsPosReal.mem_slitPlane`.
- `hasFDerivAt_cpow_comp`: the chain rule for `x ↦ T(x)^σ` where `T(x)` lies in the slit
  plane.
- `exists_fderiv_weighted`: if `φ` is real differentiable and `φ · D^N = ω · P` with
  `P ∈ degLE ι a`, then for every vector field `W` whose coordinates have degree `≤ w` there is
  `P' ∈ degLE ι (a + |κ| e + w)` with `Dφ[W] · D^{N+1} = ω · P'`. Explicitly
  `P' = Q P + D · DP[W] - N P · DD[W]` with `Q = ∑_j σ_j DT_j[W] ∏_{j' ≠ j} T_{j'}`, obtained
  by differentiating the relation and using `Dω[W] · D = ω Q`.

## Provenance

Internal infrastructure for the growth bound `ComplexLinkedSmallGrowthStatement`,
one of the two growth statements of the dimension-count route to
`ComplexLinkedLanglandsQuotientNotLargeStatement` in the Library module
`ComplexLinkedLanglandsQuotientGrowth`; see `ComplexLinkedSmallGrowthProof.md` for how the pieces
fit together. This route is an independent internal proof, not taken from the literature. The
module introduces no statement from the literature, and all its results are proved here.
