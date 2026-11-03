# Stable systems for quotients of affine étale actions

`AffineFiniteTypeFirstLevel.actionQuotientSystem` constructs a
`FiniteTypeCartesianSystem E` from an affine finite type first level of the
acting relation, an affine étale action, finite invariant affine quotient
covers of that action and its diagonal pair action, chosen quotients, and a
cartesian comparison from `E` to the quotient relation whose object map is an
isomorphism.

The proof chooses the published stable affine étale action model. It pulls
that action back over all stable levels mapping to its index, and uses the
equivariant limit action to form an action cone. Each point scheme is affine
by its pullback description. Its structure map to the stable object scheme is
étale, so it is of finite type over the absolute terminal scheme. The two
covers then give the required quotient system through
`ActionDiagram.finiteTypeCartesianSystemOfCovers`.

This is an internal consequence of the published stable-system, action
descent, quotient-diagram and invariant-cover descent constructions. Its
mathematical provenance is the descent and scheme-quotient step in the proof
of Stacks Project Proposition 70.8.1, Tag 07SU, in the registered source
`stacks-noetherian-approximation-2026-11-01`. It does not assume that finite
level quotients have already been supplied.
