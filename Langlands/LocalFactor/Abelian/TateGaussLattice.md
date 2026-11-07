# Gauss integrals over valuation lattices

Worker 1248. Internal lemmas, derived from the published definitions, the
Library lattice-character integrals (`subgroup_character_integral_of_trivial`,
`subgroup_character_integral_of_nontrivial`) and the lemmas above.

* `setIntegral_additiveLattice_character`: for `ψ` of conductor `n`, the integral of
  `ψ` over `π^(-M) O` is its mass when `M ≤ n` and `0` otherwise;
  `setIntegral_gaussShell_character` gives shell integrals as differences.
* `indicator_gaussIntegrand_eq_zetaIntegrand`: on `π^(-M) O` with `M ≤ n` the Gauss
  integrand of `(χ, ψ)` at `s` is the zeta integrand of the lattice indicator for
  `χ⁻¹` at `1 - s`. Hence the Gauss integrand is integrable on every
  `π^(-(n+j)) O` when the zeta integral of `χ⁻¹` converges at `1 - s`
  (`gaussIntegrand_integrableOn_additiveLattice`), and its integral over
  `π^(-n) O` is a lattice zeta integral (`setIntegral_additiveLattice_gauss_base`).
* `setIntegral_additiveLattice_gauss_ramified`: for conductor `a ≥ 1`, the integral
  over `π^(-(n+j)) O` is `ε(s)` if `a ≤ j` and `0` otherwise (induction on `j`, adding
  one shell at a time and using Gauss shell vanishing).
* `setIntegral_gaussShell_unramified`, `setIntegral_additiveLattice_gauss_unramified`:
  for conductor `0` the integrand on the shell of order `-D` is
  `(χ(π) q^(-s))^D ψ`; for `j ≥ 1` the integral over `π^(-(n+j)) O` is the integral
  over `π^(-n) O` minus `(χ(π) q^(-s))^(n+1) μ(π^(-n) O)`.
