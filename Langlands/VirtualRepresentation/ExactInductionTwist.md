# Twists, restriction and induction on the actual exact quotient

Worker 1763 derives this auxiliary unit for fixed-Haar duality task
`e945d920-df9f-446c-9528-b488a3bee609`.

The actual representation equivalence `induceTwistEquiv` specializes
`Langlands.coindTwistEquiv` to subgroup inclusion and the finite-dimensional
equivariant-function model already used by `FiniteRepresentation.induce`.
It identifies induction of a restricted character twist with the ambient
character twist of induction, with independent coefficient, group and
representation-carrier universes.

On the continuous exact Grothendieck groups,
`continuousRestrict_continuousTwist` proves that restriction along a continuous
group homomorphism commutes with twisting by the pulled-back continuous
character. On actual representation classes the actions are definitionally
identical; the universal property of the exact quotient gives the identity
on all virtual elements.

`continuousInduce` specializes the existing exact induction map to ordinary
continuous complex representations of an open finite-index subgroup. It
uses the proved usual-topology continuity of actual induction; no closure
condition is an additional input. The carrier universe of its codomain is
the maximum of the group and source carrier universes, as in the existing
induction construction.

`continuousInduce_continuousTwist` is the corresponding continuous-character
projection formula on all exact virtual elements. Equality of integer-linear
maps reduces to actual representation classes, where `induceTwistEquiv`
supplies a genuine intertwining equivalence. The quotient retains every
short exact relation and does not assume semisimplicity or finite image.

This is internal derived algebra and continuity from the named published
constructors and the explicit coinduced-function equivalence. It does not
assert the dual-induction identity or a local-constant functional equation.
