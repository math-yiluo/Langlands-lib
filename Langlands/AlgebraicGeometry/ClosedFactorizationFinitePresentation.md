# Finite presentation of closed factorization loci

`ClosedFactorizationFinitePresentation.model` constructs an actual closed
locus over an affine base for a whole-product factorization condition.
The structural morphism of the first factor is affine and flat, and its
coordinate module is projective over the base ring. The prescribed closed
immersion into the product is locally of finite presentation. The model
supplies the closed immersion into the second factor and its local finite
presentation, along with the factorization equivalence for every relative
test scheme. It uses the identity base extension to apply the published
closed-factorization construction.

Over an affine base, let `X` be affine with projective coordinate module.
Let `d : D ⟶ X ⊗ Y` be a closed immersion locally of finite presentation.
The theorem `ClosedFactorizationFinitePresentation.locallyOfFinitePresentation_of_represents`
shows that a closed immersion `i : Z ⟶ Y` representing whole-product
factorization through `d` is locally of finite presentation. The hypothesis
on representation is the equivalence on all relative test schemes used by
`ClosedFactorizationLocusProof.closedFactorizationLocus`.

On an affine chart of `Y`, the coordinate ideal of `D` in the product is
finitely generated. Projectivity of the coordinate module of `X` gives a
finitely generated coefficient ideal in the chart algebra. The quotient by
that ideal represents the same factorization condition on affine tests.
Applying the universal properties to the two affine closed subschemes gives
inverse maps over the chart. Locality on the target then gives local finite
presentation for the original representative.

This is an internal application of the Library's affine product factorization
theorem and finite generation of projective tensor coefficient ideals.
