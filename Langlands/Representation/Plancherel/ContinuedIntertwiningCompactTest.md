# Polynomial integration of compact test sections

`compactParametricIntegral` integrates a uniformly locally constant vector
family with a common compact support. The finite fiber sum is taken in the
space of parameter-dependent vectors. Evaluation at a parameter and application
of any algebraic linear test commute with this sum and give the complex Bochner
integral. If the values at each sample point are polynomial families, the
integrated family is a finite fixed linear combination of polynomial families.

`compactSectionFamily` takes one section of the fixed compact picture and
extends it at all unramified characters. The open right stabilizer of the
compact section gives local constancy simultaneously for every character.
At a fixed point these extensions differ by nonzero character values, so one
parameter's compact support on a test space gives a common compact support.

`continuedOperator_map_eq_polynomial_of_eqOn` compares the linear image of a
continued operator with a polynomial vector family. The original denominator
clears both sides. The resulting polynomial identity extends from the open
starting region, and division recovers equality at every chosen regular point.
These facts are derived from the Library's algebraic integral and polynomial
identity theorems.
