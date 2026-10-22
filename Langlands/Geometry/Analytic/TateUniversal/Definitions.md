# Tate coordinates and continuous maps from bounded algebra maps

Author: Worker 36.

`BoundedAlgHom.toContinuousLinearMap` is the existing algebra map's scalar
linear map bundled with its proved positive norm bound. Its underlying
function is unchanged and it is continuous. These facts are intrinsic to
the construction, using Mathlib's bounded-linear-map interface.

`StrictTateAlgebra.X` is the actual restricted monomial of exponent one in
one coordinate and coefficient one. Its norm is one by the previously
proved monomial norm formula and the normed field's unit norm. Neither
this coordinate nor the bounded map wrapper assumes an evaluation or
universal-property theorem. Those assertions are in the separate Statement
module, whose proofs are not imported here.

This is an internal coordinate interface for the unit-radius convergent
power-series algebra in Berkovich's Trieste 2009 lectures, Example 1.2.2(v),
p.4, and the coordinate-prescribing bounded extensions in Exercise 2.1.5(i),
pp.7-8. The continuous linear map wrapper is an implementation device for
actual bounded algebra homomorphisms. Coefficient and variable types may
be arbitrary, with the hypotheses written in each definition.
Registered original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
