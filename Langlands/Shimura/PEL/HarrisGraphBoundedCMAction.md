# Finite joint Harris action loci with specified graph polynomials

Fix the original Harris arithmetic, signature, field map, positive
auxiliary involution and duality data. On a noetherian affine base,
choose a `ProjectiveEndomorphismGraphPieces` presentation for the
abelian family. `GraphBoundedCMAction.actionTupleInclusion` is the
closed inclusion of the existing joint integral action, determinant
and Rosati locus into the finite tuple of relative endomorphisms,
using `comparisonAllTests`. `GraphBoundedCMAction.actionOf` is the
classified actual integral action. The lemma
`GraphBoundedCMAction.coordinate_classifies_basis` identifies each
coordinate with the image of the corresponding order basis element.

Choose one graph polynomial for each basis element.
`GraphBoundedCMAction.scheme` is the pullback of the closed
inclusion along the product of the corresponding graph pieces.
Every graph piece is finite over the base by `open_isFinite`.
Finite products preserve this property and the pulled-back closed
inclusion is finite, which makes the constructed scheme finite.

`GraphBoundedCMAction.inclusion` forgets the bounds and is a
monomorphism. `GraphBoundedCMAction.factors_iff` tests factorization
through it by containment of each coordinate's image in the specified
piece. In one direction this follows from the pullback equation.
In the other direction the open immersion lifting property yields
the coordinate maps into the specified pieces. The finite product and
pullback assemble them into the factorization.

`GraphBoundedCMAction.factors_of_geometric_graphPolynomials` uses
this criterion after computing the section dimensions on geometric
points. For each point of a test, take the map from an algebraic
closure of its residue field. The section dimensions over that field
identify the piece of each basis coordinate, giving containment of
each coordinate's image over the entire test.
