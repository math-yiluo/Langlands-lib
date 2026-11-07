# Vanishing of ramified Gauss integrals off the conductor shell

Worker 1248. Internal lemmas, derived from the published definitions. For a
quasicharacter `χ` of positive conductor `a` and an additive character `ψ`, the
Gauss integral of `χ⁻¹(x) |x|^(-s) ψ(x)` over the shell of order `-d` vanishes
unless `d = n + a`, where `n` is the conductor of `ψ`. This is the standard
computation behind Tate's ramified epsilon factor.

* `setIntegral_gaussShell_mul_unit`: multiplication by a unit of order zero
  preserves each shell and the Haar measure (scalar Haar scaling).
* `setIntegral_gaussShell_add`: translation by an element of strictly smaller
  valuation preserves a shell.
* `gauss_shell_integral_eq_zero_of_lt`: if `ψ` is trivial on the lattice of level
  `m` and `d < m + a`, rotate by a principal unit `u` of level `max(0, d - m)` with
  `χ(u) ≠ 1` (it exists below the conductor); `ψ(ux) = ψ(x)` on the shell, so the
  integral equals `χ(u)⁻¹` times itself.
* `gauss_shell_integral_eq_zero_of_gt`: if `ψ(x₀) ≠ 1` for some `x₀` in the lattice of
  level `m + 1` and `d > m + a`, translate by `x₀`; `χ` is unchanged because
  `1 + x₀/x` is a principal unit of level `a`, so the integral equals `ψ(x₀)` times
  itself.
* `gauss_shell_integral_eq_zero`: the two cases at the conductor `n`, for every `s`.
