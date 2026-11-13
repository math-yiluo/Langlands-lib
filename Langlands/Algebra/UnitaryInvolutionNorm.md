# Unitary involutions and the regular norm

Helper module for the proof of `Langlands.LocalUnitaryDivisionCommutativeStatement`.

Throughout, `L` is a field, `D` a division ring that is an `L`-algebra, `σ : L →+* L`, and
`τ : D → D` satisfies `Langlands.IsUnitaryInvolution σ τ` (additive, `τ (x * y) = τ y * τ x`,
`τ (τ x) = x`, `τ (algebraMap L D c) = algebraMap L D (σ c)`).

## Elementary consequences

`addHom` packages `τ` as an additive map. The lemmas `tau_zero`, `tau_neg`, `tau_sub`,
`tau_mul`, `tau_tau`, `tau_algebraMap`, `tau_one`, `tau_pow` (`τ (x ^ n) = τ x ^ n`, by
induction using anti-multiplicativity), `tau_smul` (`τ (c • x) = σ c • τ x`), `sigma_invol`
(`σ (σ c) = c`, obtained by applying `τ` twice to `algebraMap L D c`), `injective` and
`tau_inv` (`τ x⁻¹ = (τ x)⁻¹`) are direct. `tauUnit hτ j` is the unit `τ j` for a unit `j`.

`tau_aeval`: for a polynomial `p` over `L`, `τ (aeval x p) = aeval (τ x) (p.map σ)`; proved by
induction on `p` through sums of monomials, using `tau_pow`, `tau_algebraMap` and the fact that
scalars are central.

## Minimal polynomials and norms

Assume `D` is finite-dimensional over `L`.

* `minpoly_eq`: `minpoly L (τ x) = (minpoly L x).map σ`. By `tau_aeval`, `τ x` is a root of
  the monic polynomial `(minpoly L x).map σ`, and `x = τ (τ x)` is a root of
  `(minpoly L (τ x)).map σ`; the two divisibilities give equal degrees, and a monic divisor of a
  monic polynomial of the same degree equals it.
* `adjoinRank L x` is the dimension of `D` over the commutative subalgebra `L[x]`
  (`residueGeneratorSubalgebra L D x`, a field), with `D` a module by left multiplication.
  `finrank_eq_natDegree_mul_adjoinRank`: `[D : L] = deg(minpoly x) · adjoinRank L x` (tower law).
* `norm_eq_minpoly_coeff`: the regular norm `Algebra.norm L x` (determinant of left
  multiplication on `D`) equals `((-1)^deg · (minpoly L x).coeff 0) ^ adjoinRank L x`. Left
  multiplication by `x` is the restriction of scalars of the `L[x]`-linear map `x • id`, so
  `LinearMap.det_restrictScalars` gives the field norm of `x` over `L` raised to `adjoinRank`,
  and the field norm of the power-basis generator is `(-1)^deg` times the constant coefficient
  of its minimal polynomial.
* `norm_tau`: `Algebra.norm L (τ x) = σ (Algebra.norm L x)`, combining the previous items:
  `τ x` has the same minimal-polynomial degree and hence the same `adjoinRank`, and its
  constant coefficient is `σ` of that of `x`.
