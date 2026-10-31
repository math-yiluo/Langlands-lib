# Principal symbol of the actual monic Cartan polynomial operator

This proof imports the actual published fixed-basis coefficient
construction and the ambient Cartan covector form. For every number field in any
universe, every natural rank, every monic complex polynomial, every ambient matrix
and every real continuous covector, it proves that
`cartanPolynomialCoordinateOperator K n p` has principal symbol equal to the
complex embedding of `ambientCartanCovectorForm K n y ξ`, raised to `p.natDegree`.
This includes rank zero and constant monic polynomials and uses the original
normed matrix carrier throughout.

The internal proof follows the published recurrence. A private top-order array
symbol is the finite ordered-word sum weighted by covector values on the fixed
basis. At the new top order a left directional composition has no differentiated
old coefficient; only the prepended field-coordinate term remains. Splitting a
word into its head and tail and using the basis expansion of the field gives the
old symbol multiplied by the covector evaluated on that field. Applying this
twice and summing over every actual Cartan direction multiplies the symbol by
the actual ambient quadratic covector form. Induction gives its power for each
Cartan iterate; the zero iterate has symbol one, including when the basis is empty.

At the declared polynomial top order, every supported lower iterate has zero
extended coefficient. Monicity leaves exactly the highest iterate with scalar
coefficient one. Its symbol is the required quadratic-form power. The argument
uses the finite polynomial support and its natural-degree bound; it makes no
positive-degree assumption.

This is derived correctness of the explicit construction rather than an external
literature theorem. This module does not prove equality of differential actions, ellipticity,
analytic regularity or the parent joint-finite analyticity theorem.

## Declarations

The public theorem is
`Langlands.Global.ArchimedeanGL.cartanPolynomialCoordinateOperator_principalSymbol`.
Fix `K : Type u` with `[Field K] [NumberField K]`, `n : ℕ`, and
`p : Polynomial ℂ` with `p.Monic`. For every ambient matrix
`y : ArchimedeanMatrix K n` and every `ξ : ArchimedeanMatrix K n →L[ℝ] ℝ`,
the theorem proves
`(cartanPolynomialCoordinateOperator K n p).principalSymbol y ξ =
(ambientCartanCovectorForm K n y ξ : ℂ) ^ p.natDegree`.

The private definition `cartanArraySymbol` is the published
`CoordinateScalarOperator.principalSymbol` formula, written for a bare
coefficient array with the fixed basis `cartanCoordinateBasis K n`. The private
lemmas carry out the following steps:

- `cartanArraySymbol_left`: one left composition multiplies the symbol by
  `ξ (V y)`;
- `cartanArraySymbol_squareSum`: the square sum multiplies it by the covector
  form;
- `cartanIterateCoefficients_principalSymbol`: the iterate's symbol is the
  corresponding power of the covector form;
- `cartanPolynomialCoordinateOperator_top`: for monic `p`, the top-order
  coefficient comes from the highest iterate.

Worker 116 authored this module. Worker 880 checked it and prepared it for
review.
