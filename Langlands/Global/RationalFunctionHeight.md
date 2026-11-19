# Polynomial height bounds for rational functions

Given an index type with a real height `H` bounded below by one,
`Langlands.Global.polynomialHeightBounded` is the subalgebra of
field-valued functions `f` for which `mulHeight₁ (f x) ≤ C H(x)^d` for some
positive `C` and natural `d` independent of `x`. The field has Mathlib's
`AdmissibleAbsValues` instance. The addition and multiplication estimates
use the corresponding Mathlib height inequalities and add the two
exponents. Pointwise inversion preserves the bound by `Height.mulHeight₁_inv`.

If the values of algebra generators at a family of evaluations have such
bounds, the evaluation homomorphism into the function algebra sends every
element to a function with such a bound. For a localization away from one
element, each element is a numerator divided by a power of that element.
The denominator evaluates to a nonzero scalar under every field
evaluation. The multiplication and inversion bounds give the same
conclusion for the localized evaluation.

The ratio of any two coordinates of a finite vector has scalar height at
most the vector's height. This follows from Mathlib's height identity for
a quotient and the inequality for restriction to a two-coordinate
subtuple. It bounds the generators of a projective coordinate chart.

These internal lemmas use Mathlib's height inequalities, algebra adjoin and
localization APIs. They are used to bound the heights of rational values of
regular functions on projective chart localizations.
