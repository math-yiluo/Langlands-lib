# Finite products of finite coordinate algebras

This internal derived construction packages the varying finite ranks of a
permutation atlas into an algebra over the finite product of its chart rings.

`coefficientAlgebra` and `scalarMap` give the algebra structure on families
`z a i` over base families `b a`, with scalar map `b a` constant in `i`.
The outer index and each coordinate type are finite, but coordinate types
may be empty or have different cardinalities. Each ring may also be zero.

`finite` follows from surjectivity of each evaluation map from the base
product and finite products of finite modules. `etale` identifies each base
projection as localization at its component idempotent, hence étale, then
uses finite-product étaleness. `projective` follows from finite module,
finite presentation of the étale algebra, and flatness.

`piSwap` interchanges family indices. `tensorPi` distributes a tensor product
over finite products in both factors. `tensorCoefficients` further
distributes over the coordinate indices, giving the actual algebra equivalence
from base product tensor coefficient product to the double family of overlap
tensor rings with the target chart's coordinates. The pure-tensor formulas
specify their orientations.

All types lie in an arbitrary common universe. These are algebraic product
constructions; no cover, descent coaction, or Weil comparison is asserted.
