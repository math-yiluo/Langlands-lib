# Action correctness for the Cartan coefficient recurrence

For any number field in any universe, every natural rank, every complex
polynomial and any open subset of the original ambient matrix space, the
theorem `cartanPolynomialCoordinateOperator_action` proves that the actual
published coordinate operator acts as `cartanAmbientPolynomial` on every
complex-valued function smooth on that subset. Smoothness means
`ContDiffOn ℝ ∞`. This includes rank zero, order zero and the zero polynomial;
neither monicity nor invertibility is assumed.

This is an internal correctness proof of the published coefficient recurrence.
A private finite array action uses all bounded ordered coordinate words.
Differentiating each summand gives the derivative of its coefficient and
the next derivative word. Splitting the latter word into its head and tail,
then contracting the fixed basis coordinates against a continuous linear
derivative, identifies the prepend branch with the directional derivative of
the function factor. Finite sums of the product rule therefore identify one
left-composition array with its actual directional action.

For each Cartan direction, a second application differentiates both the first
derivative and the moving matrix field. The continuous-linear-map evaluation
product rule gives exactly the Hessian and first-order moving-frame correction
in the full published ambient operator. Local equality on the open smooth
domain permits differentiation of the first-composition identity there.
Summing over every member of the actual full real Cartan basis proves the
square-sum identity.

Zero-padding does not change the finite action: an induction on the larger
order splits off its zero last coefficient. The order-zero identity array
acts as the function itself. Induction on the Cartan iterate now applies the
square-sum identity and uses equality of local germs to compare both first
and second derivatives of the previous array action and the actual iterate.
This avoids requiring smoothness outside the open domain. Finally, the finite
polynomial support bounds each iterate's order by the declared polynomial
order; distributing finite sums and scalar multiplication and removing the
padding proves the final action equality.

All directions and norms remain those of the original real normed matrix
carrier, with complex values. This proof does not assert scalar elliptic
analytic regularity or the parent joint-finite analyticity theorem.

## Declarations

The public theorem is
`Langlands.Global.ArchimedeanGL.cartanPolynomialCoordinateOperator_action`.
Fix `K : Type u` with `[Field K] [NumberField K]`, `n : ℕ`,
`p : Polynomial ℂ` and `F : ArchimedeanMatrix K n → ℂ`. Also fix
`S : Set (ArchimedeanMatrix K n)` with `IsOpen S` and `ContDiffOn ℝ ∞ F S`.
For every `x ∈ S`, the theorem proves
`(cartanPolynomialCoordinateOperator K n p).action F x =
cartanAmbientPolynomial K n p F x`.

The private definition `cartanArrayAction` is the published
`CoordinateScalarOperator.action` formula, written for a bare coefficient array
of any order with the fixed basis `cartanCoordinateBasis K n`. The private
lemmas carry out the following steps:

- `cartanArrayAction_left`: one left directional composition;
- `cartanDirectional_second`: the Hessian and the moving-frame correction;
- `cartanArrayAction_squareSum`: the square-sum identity on an open smooth
  domain;
- `cartanArrayAction_extend`: zero padding;
- `cartanArrayAction_iterate`: induction on the iterate;
- `cartanArrayAction_finset_sum` and `cartanArrayAction_mul`: linearity.

Worker 116 authored this module. Worker 880 checked it and prepared it for
review.
