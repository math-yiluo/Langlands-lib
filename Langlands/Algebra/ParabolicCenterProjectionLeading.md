# Leading forms of the Harish-Chandra map

Module `Langlands.Algebra.ParabolicCenterProjectionLeading`, namespace
`Langlands.Algebra.ParabolicCenterProjection.GradingData`.

Fix `D : GradingData g H`.

## Restriction to the letters of grading zero

- `zeroRestrict : MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial zeroIndex ℂ` is Mathlib's `killCompl`:
  it keeps the variables of grading zero and sends the others to `0`. `coeff_zeroRestrict`: its
  coefficient at `α` is the coefficient at `α` extended by zero. `degree_embDomain`,
  `zeroRestrict_X_val`, `zeroRestrict_X_of_ne`, `zeroRestrict_ξ`: the restriction of the
  linear symbol `ξ v` keeps the coordinates of `v` of grading zero.

## Gelfand elements and central Lie elements

- `ell q = zeroRestrict (ξ (T (wt q)))`, the restricted linear form of the vector dual to the
  weight `wt q`.
- `zeroRestrict_ξ_dual_of_ne`, `adCoeff_of_φ_eq_zero`: the dual vectors `b^i` of nonzero
  grading have no coordinates of grading zero, and for `φ i = 0` the matrix of `ad (b i)` is
  diagonal with entries `wt q (b i)`.
- `zeroRestrict_symbolMatrix`: the restriction of the symbol matrix `Ξ` of the Gelfand matrix
  is the diagonal matrix with entries `ell q`.
- `zeroRestrict_symbol_gelfand`: the restriction of `symbol n (gelfand n) = trace (Ξ ^ n)` is the
  power sum `∑ q, ell q ^ n`.
- `zeroRestrict_symbol_ι`: the restriction of the symbol of `ι c` is `zeroRestrict (ξ c)`.

## Leading forms of the Harish-Chandra map

For `j`, `P` and `hP` as in `Langlands.Algebra.ParabolicCenterProjectionCoordinates`:

- `hcMap_degLE`: for `z ∈ U_n`, `hcMap P z` has degree at most `n` (`coeff_hcMap` and
  `coeff_pbwPoly_eq_zero_of_mem`).
- `homogeneousComponent_hcMap`: its homogeneous component of degree `n` is
  `zeroRestrict (symbol n z)`; both have coefficients the PBW coordinates of `z` of degree `n`
  supported on letters of grading zero.
- `degLT_sub_homogeneousComponent`: a polynomial of degree at most `n` differs from its
  degree-`n` component in degrees below `n`.

## Provenance

Internal. In the classical theory the top-degree part of the Harish-Chandra image of a central
element is the restriction to the Cartan subalgebra of its symbol, an invariant polynomial; for
the Gelfand elements of the adjoint representation these restrictions are the power sums of the
roots, transported to the Cartan subalgebra by the invariant form.
