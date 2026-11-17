# Global root-group coordinates from a free actual root weight

This internal construction combines the actual root Lie comparison, explicit
corepresentation cotangent duality and global graded-line polynomiality for
Task 6700. No new external source assertion is used.

The quotient augmentation is the actual corepresentation counit: pullback
along the actual contracting-group inclusion is the quotient map and
homomorphisms preserve counits.

Fixed torus-equivariant additive-group field fibres give universal graded-line
fibre maps. Their coordinate-degree component generates the original algebra.
The actual free root Lie line identifies the root-group Lie module. Smooth
cotangent reflexivity and the explicit Lie/cotangent duality trivialize the
identity cotangent. The degree/cotangent comparison then trivializes the
coordinate-degree component. Global graded-line polynomiality supplies an
actual homogeneous polynomial coordinate over the original ring.

The field-fibre input is the actual `HasEquivariantFibres` condition, with a
fixed exponent character and positive integral pairing with the contracting
cocharacter. The ambient group is affine and smooth, the same character has
zero pairing with the centralizing cocharacter, and its actual ambient
exponent weight has an explicitly supplied linear trivialization.
These assumptions suffice over every commutative base in universe u,
including the zero ring. No connectedness, reducedness, localness or field
hypothesis is added to the base.

`rootCoordinateDegreeEquiv` constructs the degree trivialization and
`exists_coordinate_of_free_weight` constructs the actual polynomial
coordinate. Establishing its weight under the whole torus and assembling the
actual root parametrization remain separate steps of the host task.
