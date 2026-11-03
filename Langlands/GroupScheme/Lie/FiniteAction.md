# Finite coordinates for the actual Lie action

`Lie.FiniteCoordinates U d` describes linear coordinates on the actual module
`Additive (lieKernel U A)` for every commutative test algebra `A`, with
naturality under every algebra map. Here the base is any commutative ring and
`U` has affine structure morphism. The datum contains neither a representation
nor a determinant character. It allows `d = 0` and makes no splitting,
reducedness, characteristic, smoothness or finite-type assumption.

For an actual `AutomorphicAction H U`, `coordinateAction` transports the
published differential to `Fin d → A`; `coordinateMatrix` is its invertible
matrix. The action and matrix homomorphism laws follow from the original
action. The naturality theorem for the action follows from differential
naturality and the coordinate comparison; evaluating it at the coordinate
vectors proves matrix naturality over every test-algebra map.

When `H` is affine as a scheme, `AffineCoordinates.actualPointsEquiv` identifies
the chosen corepresented functor with the actual points of `H`, naturally in
all algebras. The affine-source adapter `matrixRepresentationOfAffinePoints`
uses this comparison and the published general linear corepresentation.
Naturality gives a map of corepresented group functors and hence an actual
group-scheme morphism. Its affine matrix recovery theorem cancels the
corepresented point comparisons and the source isomorphism.

`AutomorphicAction.finiteRepresentation` applies the adapter to the constructed
coordinate matrices. Its `finiteRepresentation_affineMatrix` theorem recovers
those matrices, while `finiteRepresentation_affineAction` identifies the
resulting action with the original differential under the chosen coordinates,
for every test algebra and every actual acting point.

This is an internal construction from the published differential,
corepresented Yoneda and matrix-representation infrastructure. Finite
coordinates remain a hypothesis of this construction. Structural existence
for dynamic unipotent subgroups is a separate proposition with smoothness and
finite-dimensionality as conclusions.
