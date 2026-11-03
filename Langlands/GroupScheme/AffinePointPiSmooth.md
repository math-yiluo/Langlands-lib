# Coordinate-smooth families over finite coefficient products

Let `G` be an affine group scheme over a commutative base ring `R`, and let
`A i` be a dependent family of commutative `R`-algebras indexed by a finite
type `J` in the base universe. For each index choose any ring homomorphism
`c i : A i →+* B i`, where `B i` is a normed commutative real algebra.
The universe of `B i` is independent of the base universe. The source of a
parameter family is any space `M` with a real model with corners `I` and
a compatible charted-space structure. No `IsManifold` instance is required.

`affinePointPiCoefficientMap` applies the specified coefficient maps
componentwise. `coordinateSmooth_pi_iff` states that a family of actual points
over `Π i, A i` is `CoordinateSmooth` for this coefficient map exactly when
each projected family is `CoordinateSmooth` for its specified `c i`. These
are the existing tests on every global regular function on the original
scheme. This is a finite product result: the smooth test algebra
`Π i, B i` uses its standard finite product normed-space manifold.

The proof uses `contMDiff_pi_space` to check smoothness of a finite dependent
product componentwise. The proved regular-function evaluation identity for
`affinePointsEval` identifies each component with the original regular-function
test at the projected point. Thus both directions use exactly the same
regular functions. `coordinateSmooth_affinePointPi` proves smoothness of actual
point assembly. `coordinateSmoothPiFamilyEquiv` bundles projection and assembly
into an equivalence between the indicated subtypes of families; its inverse
laws are the proved actual point-product inverse laws.

The accompanying change to `AffinePointCoordinateSmooth` makes only the
universe of its smooth test algebra independent of the base and coefficient
universe. Its definition and preservation proofs are otherwise unchanged.
This allows tests with ordinary real or complex values for coefficient
rings in any universe.

This internal derived construction uses the universal property of actual
coefficient products, the existing regular-function criterion and pinned
Mathlib's finite product smoothness theorem. It assumes no topology on `A i`,
continuity of `c i`, smoothness or reductivity of `G`, or manifold structure on
the group of actual points. It does not yet identify these tests with
manifold smoothness for an algebraic group or prove any measure or growth
theorem.
