# Determinant shells of the corank-one integral

Internal helper for the proof of `HighlyRamifiedGammaStabilityStatement`. It specializes
`ShellExpansion` to the published corank-one integrand on
`N_(m+1) \ GL_(m+1)` with the published determinant order and slices of `DeterminantSlices`.
Sources: Jacquet, Piatetski-Shapiro and Shalika 1983, (4.2.1)–(4.2.2), printed pages
406–407 (slices and the Laurent expansion), and Jacquet–Shalika 1985, Corollary (3.3)
(printed pages 325–326), as used in §4.4 on printed page 329.

- `determinantWeight_eq_spectral`: `|det g|^s = (q^(-s))^(ord det g)`, from the published
  `determinantWeight_eq_spectralPoint_zpow` and `normalizedAbs_of_ne_zero`.
- `corankOneIntegrand_eq_mul_spectral`: the published `corankOneIntegrand` at `s` is the
  integrand at `0` times `(q^(-s))^(determinantOrder)`, since
  `|det|^(s-1/2) = |det|^(-1/2) |det|^s`.
- `exists_order_lower_bound`: for a Whittaker function `U` on `GL_(m+2)` that is right
  invariant under an open subgroup, `U(diag(g,1)) ≠ 0` forces `ord det g ≥ j₀` for one
  integer `j₀`. Write `g = u · diag(a) · κ` (published
  `CommonLevel.exists_unipotent_diagonal_integral`). The published root bound
  (`CommonLevel.root_bound`, `CommonLevel.corank_diagonal_upper`) gives `|a_i| ≤ M`, so
  `|det g| ≤ M^(m+1)`.
- `corankOne_shell_eq_of_const`: if moreover the corank-one integral converges absolutely at
  one real `s₀` and equals `C` for `Re s > a`, then the integral of the integrand at `0` over
  the slice `determinantSlice … m j` is `C` for `j = 0` and `0` otherwise
  (`shell_integral_eq_of_const`).
