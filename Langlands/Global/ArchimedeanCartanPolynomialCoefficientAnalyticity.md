# Coefficient analyticity for the explicit Cartan recurrence

This module imports the published coefficient construction
`Langlands.Global.ArchimedeanCartanPolynomialCoefficients`.
It proves that every finite iterate coefficient is real
analytic on the full original ambient matrix space, and consequently that
`cartanPolynomialCoordinateOperator K n p` has analytic coefficients
there for every complex polynomial. No monicity is needed for these
coefficient claims.

The proof follows the actual recursive definitions. The moving Cartan
fields are continuous real linear maps, and each fixed basis coordinate
is continuous because the original space is finite dimensional. The
complex inclusion of a real coordinate is continuous and real linear.
The real derivative of an analytic complex-valued coefficient is
analytic by Mathlib's `AnalyticAt.fderiv`; its application to an analytic
field is the composition of the continuous bilinear evaluation map
with a pair of analytic functions. Zero padding preserves analyticity
because the branch depends only on natural-number orders. Products,
sums, the two directional compositions, induction on the iterate and
the finite polynomial sum preserve analyticity.

This is an internal correctness argument for the explicit recurrence.
It does not prove equality of operator action, the highest-order
symbol, ellipticity, analytic regularity or joint-finite analyticity.
No external theorem is being asserted as formalized.

## Declarations

All declarations are in the namespace `Langlands.Global.ArchimedeanGL`, with
`K : Type u` a number field and `n : ℕ`.

- `analyticAt_cartanMovingField K n i x` states that the moving Cartan field
  `cartanMatrixField K n i`, the map
  `y ↦ y * realLieAlgebraToMatrix K n (cartanAdaptedBasis K n i)`, is
  `AnalyticAt ℝ` at every ambient matrix `x`. It is a continuous real linear map.
- `analyticOnNhd_cartanLeftDirectionalCoefficients K n V hV a ha` states the
  following. Suppose the field `V` and every coefficient `a k w` are
  `AnalyticOnNhd ℝ` on `Set.univ`. Then every coefficient of
  `cartanLeftDirectionalCoefficients K n a V` is also analytic on `Set.univ`.
- `cartanIterateCoefficients_analytic K n m` states that every coefficient
  `cartanIterateCoefficients K n m k w` is `AnalyticOnNhd ℝ` on `Set.univ`.
- `cartanPolynomialCoordinateOperator_analyticCoefficients K n p` states
  `(cartanPolynomialCoordinateOperator K n p).AnalyticCoefficientsOn Set.univ`
  for every `p : Polynomial ℂ`.

The private lemmas handle the following steps:

- `analyticAt_directionalCoefficient`: the directional derivative coefficient
  `y ↦ fderiv ℝ a y (V y)`;
- `analyticOnNhd_cartanCoefficientExtend`: zero padding;
- `analyticOnNhd_cartanPrependCoefficient`: the prepend term;
- `analyticOnNhd_cartanSquareSumCoefficients`: the Cartan square sum.

Worker 116 authored this module. Worker 880 checked it and prepared it for
review.
