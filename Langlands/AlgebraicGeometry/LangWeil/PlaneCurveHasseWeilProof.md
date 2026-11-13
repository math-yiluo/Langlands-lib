# Proof of Schmidt's Hasse–Weil bound for plane curves

Author: Worker 5406, with Worker 81 and Worker 78 (helper modules, see below). The reduction
module `PlaneCurveHasseWeilReduction` was written by Worker 96 of an earlier instance and is
used unchanged.

`planeCurveHasseWeil : PlaneCurveHasseWeilStatement.{u}` proves the Library statement
`Langlands.AlgebraicGeometry.LangWeil.PlaneCurveHasseWeilStatement` with no extra hypotheses.
That statement is Schmidt's theorem (W. M. Schmidt, *Zur Methode von Stepanov*, Acta Arith. 24
(1973), Satz, printed p. 347). Let `F` be a finite field with `q` elements and let
`f ∈ F[X, Y]` be absolutely irreducible, of degree `m > 0` in `X` and `n > 0` in `Y`. If
`q > 9 (m + 1)² (n + 1)²`, then the number `A` of zeros of `f` in `F²` satisfies
`|A - q| < 2 min(m² n, n² m) √q`.

## Proof

The proof is the single application

`planeCurveHasseWeil_of_stepanov Stepanov.stepanovNormPolynomials planeCurveElementaryReductions`.

- `planeCurveHasseWeil_of_stepanov` (`PlaneCurveHasseWeilReduction.lean`) shows that
  `StepanovNormPolynomialsStatement` and `PlaneCurveElementaryReductionsStatement` together
  imply the target. The rational zero count is the sum of the vertical fibre counts. The
  elementary reductions replace `f` by a polynomial with the same zero count, both partial
  derivatives nonzero and ordered degrees. In the linear case `n = 1` the bound is elementary.
  Otherwise the Library theorem `stepanovCounting` turns the two auxiliary polynomials into
  the bound.
- `planeCurveElementaryReductions` is already proved in the Library
  (`PlaneCurveElementaryReductionsProof.lean`).
- `Stepanov.stepanovNormPolynomials` (`Stepanov/NormPolynomials.lean`) proves
  `StepanovNormPolynomialsStatement`. It builds the two auxiliary polynomials of Stepanov's
  method in Schmidt's version, Hilfssatz 3–6. The helper modules under `Stepanov/` contain the
  pieces; each has its own Markdown file:
  - `Box`, `Taylor`, `Branch`, `Norm`, `PointBranch`, `Construction`, `Assembly`,
    `NormPolynomials` (Worker 5406);
  - `ResultantDegree`, `GoodSet`, `DivisibleKernel`, `RootTools` (Worker 81);
  - `BivariateModel` (Worker 5406), which transfers the hypotheses from
    `MvPolynomial (Fin 2) F` to `F[X][Y]`;
  - `FrobeniusIndependence`, Schmidt's Hilfssatz 3, and `ParameterArithmetic`, the parameter
    inequalities (Worker 78).

No Lang–Weil, Hasse–Weil, Weil-conjecture or Bertini input is assumed anywhere. Every
ingredient is either in the Library or proved in these modules from Mathlib.
