# The valuation of a prime element of a factorial chart

This internal helper module works in the setting of
`Langlands.CommutativeAlgebra.ChartUniqueFactorization`: `A` is a domain with
fraction field `K`, `S` is an `A`-subalgebra of `K`, and `chartLoc K S Q` is the
localization `S_Q` inside `K`. It is used to verify the discrete-valuation
hypotheses of `uniqueFactorizationMonoid_of_chart` for the boundary divisors in
the proof of `SplitSimplyConnectedFactorialStatement`.

- `mem_chartLoc`: membership in `S_Q` means being a fraction `a / s` with
  `a, s ∈ S` and `s ∉ Q`.
- `mem_chartLoc_of_notMem`: an element `s ∈ S` outside `Q` and its inverse lie
  in `S_Q`.
- `inv_notMem_chartLoc`: if `π ∈ Q` is nonzero in `K`, then `π⁻¹ ∉ S_Q`. A
  fraction `a / s = π⁻¹` would give `s = π a ∈ Q`.
- `exists_zpow_mul_unit`: if `S` is a unique factorization monoid and `π ∈ S` is
  prime, then every nonzero `x ∈ K` has the form `π ^ n · u` with `n ∈ ℤ` and
  `u, u⁻¹ ∈ S_{(π)}`. The proof writes `x = a / b` with `a, b ∈ A`, factors the
  images of `a` and `b` in `S` as `π ^ i a'` and `π ^ j b'` with `π ∤ a', b'`
  (`WfDvdMonoid.max_power_factor`), and takes `n = i - j`, `u = a' / b'`.

Provenance: internal; standard commutative algebra.
