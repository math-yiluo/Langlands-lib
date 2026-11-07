# Polynomial coordinates and Frobenius quotients of dynamic unipotent groups

Worker 1369 derives this construction from the published dynamic unipotent
action, positive augmentation weights, polynomial eigen-coordinate theorem,
tangent-coordinate comparison, and Frobenius quotient model. No external
literature statement is asserted.

Let `G` be a smooth affine group over an arbitrary field `k : Type u`, let
`i : T → G` be a supplied split torus morphism, and let `ν` be any
cocharacter of `T`. No maximality, genericity, root datum, algebraic
closedness, or positive characteristic is needed for the coordinate
construction. The source `U` is the existing actual group scheme
`Standard.unipotentScheme i ν ∅`. Its inclusion represents the dynamic
unipotent subgroup of `ν` on all relative scheme tests.

`UnipotentPolynomialCoordinates` retains a finite list of actual Lie
coordinate functions, their torus weights, bijectivity of polynomial
evaluation, vanishing at the actual identity, positive pairing of the
weights with `ν`, and their nondecreasing heights.
`unipotentPolynomialCoordinates` constructs such data: the published
representative is smooth; its augmentation weights pair positively
with `ν`; and `exists_positiveWeight_coordinates` gives the list.
Choice selects a witness of this proved existence statement.

The resulting `polynomialEquiv` is an algebra equivalence to a polynomial
algebra in `dimension` variables, and `polynomialEquiv_origin` identifies
constant coefficient with evaluation at the actual identity.
The tangent-coordinate equivalence proves that `dimension` is the
dimension of the actual identity Lie kernel. These are algebra
coordinates; the group law need not be coordinatewise addition.

In exponential characteristic `p`, at every height `r`, the existing
Frobenius coordinate model now applies without a supplied
coordinate-existence hypothesis. The actual coordinate algebra modulo
the Frobenius image of its augmentation ideal is finite dimensional,
of dimension `(p^r)^dimension`, equivalently `(p^r)^(dim Lie U)`.
Height zero and zero variables are retained.

`quotientMap_eq_zero_iff` identifies vanishing in this actual quotient
with vanishing of every polynomial coefficient whose exponent is at most
`p^r - 1` in each variable. This uses the exact ideal comparison under
the pointed algebra equivalence. It asserts no degree bound on
polynomials outside the quotient.

This construction supplies actual dynamic subgroup coordinates and the
corresponding exact Frobenius quotient. It does not prove injectivity
of restriction of an entire Steinberg covariant space to a fixed-height
quotient, a dimension bound for that entire space, or the host
`SteinbergBigCellStatement`.
