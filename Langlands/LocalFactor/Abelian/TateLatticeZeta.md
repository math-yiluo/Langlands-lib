# Lattice-coset zeta integrals

Worker 1248. Internal lemmas computing the published zeta integral
`PadicAbelian.zeta` on indicators of valuation-lattice cosets. They use Worker
1786's convergence theorem `zeta_integrable` and shell formula
`setIntegral_zeta_orderShell`.

* `cosetTest m b`: the indicator of `{z | z - b ∈ π^(-m) O}` as a Schwartz–Bruhat
  function (locally constant with compact support).
* `setIntegral_integralUnits_characterExtension`: the integral of `χ` over `O^×` is
  `μ(O^×)` when the conductor is `0` and `0` otherwise (the ramified case is the
  rotation argument of `gauss_shell_integral_eq_zero_of_lt` for `χ⁻¹` and the
  trivial additive character).
* `zeta_additiveLattice`: where the zeta integral converges, the zeta integral of
  `1_{π^(-M) O}` is `(1 - X)⁻¹ X^(-M) ∫_{O^×} χ` with `X = χ(π) q^(-s)`: the
  integral over the shells of order `i - M`, `i ≥ 0`, is a geometric series
  (`hasSum_integral_iUnion`).
* `setIntegral_preimage_mul_unit`: the substitution `x ↦ bx` on any set multiplies
  Haar integrals by `|b|⁻¹`.
* `exists_principalUnit_of_mem_coset`, `zeta_coset_of_not_mem`: a coset
  `b + π^(-m) O` with `b ∉ π^(-m) O` equals `b` times principal units of level
  `j = -m - ord b ≥ 1`. Its zeta integral is `χ(b) |b|^(s-1) μ(π^(-m) O)` if `a ≤ j`
  (the character is constant on the coset) and `0` otherwise (rotation by a
  principal unit of level `j` on which `χ` is nontrivial). No convergence hypothesis
  is needed here.
