# Evaluation and cancellation of the density factors

For a density package `P`, the density is the package constant times the
inverse of the canonical scalar.

- `packageDensity_value_of_scalarFraction`: if the scalar is `a/b` with
  regular `a`, `b`, the density at a regular point with `a(z) ≠ 0` is the
  constant times `b(z)/a(z)`.
- `packageDensity_value_of_scalar_zero`: if the scalar vanishes, the density
  value is zero at every regular point.
- `packageDensityConstant_ne_zero`: the constant is nonzero for a split
  torus.
- `package_compact_spec`: the canonical scalar is a quotient of regular
  functions, and at each common regular parameter the two actual compact
  continuations of the package compose to that value times the identity.
- `weight_mul_roundTrip_of_scalar_product`: complex arithmetic that cancels a
  density ratio against a round-trip scalar, keeping fixed nonzero factors.

The density is `µ(ω) = j(ω)⁻¹ ∏ γ(M_α|M)²` of Waldspurger V.2, printed
p. 292. The scalar `j` is defined in IV.3, printed p. 285 (source `waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`).
