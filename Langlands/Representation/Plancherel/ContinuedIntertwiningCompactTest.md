# Polynomial integration of compact test sections

`compactParametricIntegral` integrates a uniformly locally constant vector
family with a common compact support by a measure-weighted finite fiber sum in
the space of parameter-dependent vectors. When the measure is finite on compact
sets, evaluation at a parameter followed by any algebraic linear test gives an
integrable complex function, and its Bochner integral equals that test of the
fiber sum. If the values at each sample point are polynomial families, the
integrated family is a finite fixed linear combination of polynomial families.

`compactSectionFamily` takes one section of the fixed compact picture and
extends it at all unramified characters. The open right stabilizer of the
compact section gives local constancy simultaneously for every character.
At a fixed point these extensions differ by nonzero character values, so one
parameter's compact support on a test space gives a common compact support.

`continuedOperator_map_eq_polynomial_of_eqOn` compares the linear image of a
continued operator with a vector family polynomial on the whole actual character
space. Agreement on a nonempty ambient open subset of the original domain gives
a polynomial identity after clearing the original denominator. Division recovers
equality on the nonvanishing set of that denominator.
These facts are derived from the Library's algebraic integral and polynomial
identity theorems.
