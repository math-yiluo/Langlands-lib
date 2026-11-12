# Exact integral and product preimages for algebraic-space points

This derived infrastructure assembles exact coefficient-range preimages. It adapts
the argument of `AdelicFullLevelPreimageProof` to algebraic-space points using the
published product-point and separated coefficient-injectivity theorems.

`RingPoints.changeRingEquiv` packages change of coefficients along an algebra
isomorphism as an equivalence. `mem_range_of_local_lifts` assembles local lifts
using a surjective coordinate map on the source level. Separatedness identifies
the assembled point with the given point, first over the product of the local
fields, then over the original coefficient ring using its injective embedding
into that product. `preimage_eq_of_local_preimages` applies this to each local
preimage equality. No topological assertion occurs in these lemmas.

`preimage_eq_of_bijective` handles factors at which the coefficient map is an
isomorphism. `integral_preimage_of_valuative` retains the explicit hypothesis
`SpaceValuativeExistenceStatement`; it applies that statement to the spectrum of
the valuation ring with its given map to the base. A spectrum comparison from
the scalar-tower identity converts the resulting lift into a ring-valued point.
Thus this module does not prove the valuative criterion or the unconditional
proper-stage target.

The coefficient equivalence is the existing `RingPoints.changeRingEquiv X e`
from `AlgebraicSpace.RingPointsEquivalence`, with an explicit space argument
and coefficient change along `e.symm` as its inverse. It is shared with
`AdelicSpaceWeilRestrictionPoints`.
