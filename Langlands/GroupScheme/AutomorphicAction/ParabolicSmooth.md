# Smoothness of action parabolics

Internal support for the derived-group parabolic correspondence. For an automorphic action of the multiplicative group on a smooth affine group scheme over any base, every affine representative of the action parabolic is smooth.

The proof uses the actual semidirect group scheme. The acting multiplicative group lies in the centralizer, hence in the dynamic parabolic of its inclusion. Every point of that dynamic parabolic is its normal-coordinate point times its acting-coordinate point. Cancelling the second factor shows that the normal coordinate belongs to the original action parabolic.

The dynamic parabolic in the semidirect group has a smooth affine representative by the published general-base dynamic theorems. Its normal-coordinate map factors through the supplied representative of the action parabolic. The normal-factor inclusion supplies a map in the other direction. The composite on the supplied representative is the identity, by monicity of its inclusion and the coordinate identities. Smoothness follows from `AffineRetractGeometry.smooth_of_retract_anyBase`. These two maps are scheme morphisms over the base; the normal-coordinate map is not asserted to be a group homomorphism.

`parabolicNormalProjection` exposes this restricted normal-coordinate map as
an actual morphism between the underlying schemes of any supplied
representatives of the semidirect dynamic parabolic and the action parabolic.
Its composite with the latter's inclusion is the original normal coordinate,
as proved by `parabolicNormalProjection_comp`. The construction chooses a
factorization of the universal point, whose existence is
`exists_parabolicNormalProjection`; monicity of the representative's inclusion
makes this factorization unique. The smoothness proof uses this map as the
retraction in `AffineRetractGeometry.SchemeRetract`.

No noetherian, connectedness, field, or reductivity hypothesis occurs. Affineness of the supplied representative is an explicit hypothesis. The result is derived from existing actual-action and dynamic interfaces and does not assume the correspondence it supports.
