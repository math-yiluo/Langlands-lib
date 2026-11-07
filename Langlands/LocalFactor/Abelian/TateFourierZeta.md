# Zeta integrals of Fourier transforms of lattice cosets

Worker 1248. Internal lemmas.

* `zeta_const_mul`, `zeta_finset_sum`: the zeta integral is linear on finite
  combinations whose zeta integrands are integrable.
* `zeta_fourierCoset_of_mem`: if `b ∈ π^(-m) O`, then `ψ(by) = 1` on the dual lattice
  `π^(-(n-m)) O` (Library `forall_mul_eq_one_iff_mem_additiveLattice`), so
  `c ψ(by) 1_{π^(-(n-m)) O}(y)` has `c` times the lattice zeta integral.
* `zeta_fourierCoset_unit`: for a unit `b`, the zeta integral of
  `c ψ(by) 1_{π^(-L) O}(y)` for `χ⁻¹` at `1 - s` equals
  `c χ(b) |b|^(s-1)` times the Gauss integral of `(χ, ψ)` at `s` over
  `π^(-(L - ord b)) O`, by the pointwise identity
  `ψ(by) χ(y)⁻¹ |y|^(-s) = χ(b) |b|^s G(by)` and the substitution `y ↦ by`. No
  convergence hypothesis is needed.
* `fe_algebra_lattice`, `fe_algebra_shell`: the identities in a field, with
  `X = c u`, `Y = c⁻¹ r⁻¹ u⁻¹` (`c = χ(π)`, `u = q^(-s)`, `r = q`), that close the
  unramified functional equation: on a lattice
  `r^m μ(O) (1 - Y)⁻¹ Y^(m-n) V (1 - Y) = c^n (ru)^n μ(O) (1 - X)⁻¹ X^(-m) V (1 - X)`,
  and off the lattice
  `((1 - Y)⁻¹ Y^(-n) (1 - r⁻¹) μ(O) - X^(n+1) r^n μ(O)) (1 - Y) = c^n (ru)^n μ(O) (1 - X)`.
