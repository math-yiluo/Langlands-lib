# Refined opposite Jacquet exactness and binary products

Author: Worker 430.

`Langlands.Parabolic.normalizedRefinedOppositeJacquetExactness` proves
`Langlands.Parabolic.NormalizedRefinedOppositeJacquetExactnessStatement`
with four independent field and carrier universes and all ranks.

Coordinatewise inverse transpose identifies the actual refined lower
unipotent subgroup with the upper one. The published matrix membership
lemmas establish the two directions, and inverse transpose is a continuous
group involution. Pulling back a compact open subgroup containing the
image of a finite subset proves finite containment for the lower subgroup.
This proof includes rank zero and uses no classification theorem.

Restrict an input intertwiner to the actual lower subgroup. The underlying
linear map of its normalized refined Jacquet map is the generic
coinvariant map. Smoothness restricts to the subgroup, so the proved
generic coinvariant injection theorem applies using the finite-containment
result. Generic algebraic middle exactness and surjectivity prove the
right-exactness clause without smoothness.

For the product assertion, descend the two actual projections to obtain
the forward intertwiner. Descend the two inclusions and sum their
compositions with the quotient-product projections to obtain the inverse.
On representatives their compositions are the identity because
`(u,0) + (0,v) = (u,v)`. Every quotient vector has a representative, so
the two intertwiners are inverse everywhere. The resulting equivariant
linear equivalence has exactly the prescribed representative formula.
The shared positive upper-half character is already incorporated in the
published normalized map constructors.

This is an internal derivation from `OppositeRefinementFunctors`,
`UnipotentFiniteContainment`, `InverseTransposeIwahoriProof`, and
`Jacquet.ExactProof`, together with the existing product intertwiner API.
It proves no multiplicity, transitivity, reciprocity, or recovery result.
