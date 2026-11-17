# The reduced subgroup under geometric reducedness

Worker 572.

This module constructs an actual smooth reduced subgroup of a group
scheme `G` locally of finite type over any field `k`, under the explicit
hypothesis that the canonical reduced closed subscheme of `G` is
geometrically reduced over `k`. No perfect-field assumption is made.
The hypothesis is substantive: the reduction of a group over an
imperfect field need not be a subgroup without it.

`GeometricReductionSubgroup.group G` has the underlying scheme
`ReducedSubgroup.red G.X.left`. Its actual inclusion
`GeometricReductionSubgroup.inclusion G` is a closed immersion and is
surjective on underlying topological spaces. The reduced subgroup is
smooth; if `G` is affine over `k`, so is this subgroup.

The construction uses the existing canonical reduction and its
factorization property from `Langlands/GroupScheme/ReducedSubgroup.lean`.
The unit and inversion factor through the reduction because their
sources are reduced. The square of the reduction is reduced: its
projection is flat and geometrically reduced, and its base is reduced
and locally noetherian. Consequently multiplication also factors
through the reduction. The group-object descent lemma for a
monomorphism verifies all group axioms and makes the inclusion an
actual group-scheme homomorphism. Smoothness then follows from
`AlgebraicGeometry.smooth_of_grpObj`, the smoothness criterion for a
geometrically reduced group locally of finite type over a field.

This is an internal reusable construction implementing the generic
subgroup step in the proof of Conrad's Corollary A.4, author-preprint
p.29 of Prasad and Yu, *On quasi-reductive group schemes*. The
geometric-reducedness hypothesis is supplied there only after an
extension of the fraction field, using the potential-geometric-
reducedness step in A.2/A.5. This module does not construct that field
or DVR extension, or the later stable normalization.

Registered source:
`prasad-yu-2006-quasi-reductive-author-preprint`, SHA-256
`138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`.
