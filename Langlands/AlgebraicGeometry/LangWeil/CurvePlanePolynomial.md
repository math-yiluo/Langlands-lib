# Plane polynomials of monic polynomials over a one-variable polynomial ring

Lean module: `Langlands.AlgebraicGeometry.LangWeil.CurvePlanePolynomial`, namespace
`Langlands.AlgebraicGeometry.LangWeil.CurvePlane`.

This module is a helper for the proof of
`Langlands.AlgebraicGeometry.LangWeil.FamilyCurvePlaneComparisonStatement` (Task 5581).
Provenance: internal; elementary facts about bivariate polynomials, proved directly. Begun
by Worker 189 and completed by Worker 191.

## Definitions

- `planePoly F := (finSuccEquiv R 1).symm F`: a polynomial `F` in `W` over
  `MvPolynomial (Fin 1) R = R[Z]` viewed as a polynomial in two variables, `X 0 = W` and
  `X 1 = Z`.
- `diagonal := X 0 - X 1` over a field `κ`, the diagonal line.

## General facts (any commutative ring `R`)

- `finSuccEquiv_planePoly`: `finSuccEquiv R 1 (planePoly F) = F`.
- `eval_planePoly`: evaluating `planePoly F` at `v : Fin 2 → R` equals evaluating `F`,
  with coefficients evaluated at `Fin.tail v`, at `v 0` (`eval_eq_eval_mv_eval'`).
- `degreeOf_zero_planePoly`: the degree of `planePoly F` in `X 0` is `natDegree F`.
- `finSuccEquiv_map`, `map_planePoly`: `planePoly` commutes with coefficient maps; proved
  by `MvPolynomial.induction_on`.
- `irreducible_planePoly_iff`: `planePoly F` is irreducible iff `F` is (`finSuccEquiv` is a
  ring isomorphism).
- `degreeOf_map_le`: a coefficient map does not increase `degreeOf`.
- `degreeOf_coeff_le`: every coefficient of `F` has `Z`-degree at most the `X 1`-degree of
  `planePoly F` (`degreeOf_coeff_finSuccEquiv`).

## Facts over a field `κ`

- `algHom_of_eq_eval`, `eval_planePoly_algHom`, `algHomEquivZeros`: `κ`-algebra maps
  `χ : AdjoinRoot F → κ` correspond bijectively to the zeros `v ∈ κ²` of `planePoly F`, via
  `χ ↦ (χ(root), χ(Z))`; the inverse is `AdjoinRoot.liftAlgHom` of evaluation.
  `algHom_of_eq_eval_algHomEquivZeros` records that `χ` acts on coefficients as evaluation
  at the second coordinate.
- `card_zeros_planePoly_root_le`: for finite `κ`, monic `F` and nonzero `h ∈ κ[Z]`, the zeros
  `v` of `planePoly F` with `h(v 1) = 0` number at most `natDegree h * natDegree F`.
  *Proof.* `v ↦ (v 1, v 0)` injects them into the dependent sum over roots `t` of `h` of the
  roots of the monic `F(·, t)`; count roots with `Polynomial.ncard_rootSet_le`.
- `map_diagonal`, `irreducible_diagonal`, `degreeOf_zero_diagonal`,
  `degreeOf_one_diagonal`, `card_zeros_diagonal`: the diagonal is fixed by coefficient
  maps, irreducible (under `finSuccEquiv` it is `W - C Z`), has degree 1 in each variable,
  and has exactly `#κ` zeros (`v ↦ v 0`).
- `card_zeros_planePoly_of_degreeOf_one_eq_zero`: if `F` is monic, `planePoly F` is
  irreducible over `AlgebraicClosure κ`, and `planePoly F` has degree 0 in `X 1`, then
  `planePoly F` has exactly `#κ` zeros. *Proof.* All coefficients of `F` are constants
  (`degreeOf_coeff_le`), so `F = f₀` is a monic one-variable polynomial whose image over the
  algebraic closure is irreducible (`Polynomial.Monic.irreducible_of_irreducible_map`), hence
  of degree one, `f₀ = W + c`. The zeros are `{(-c, t) : t ∈ κ}`.

The last two items handle the degenerate case of the main proof, where the plane model is
a vertical line and is replaced by the diagonal, which has positive degree in both
variables and the same number of zeros.
