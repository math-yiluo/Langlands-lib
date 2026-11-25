# Normal idempotents of almost-simple field groups

`almostSimpleNormalIdempotent` proves the exact
`AlmostSimpleNormalIdempotentStatement` in every universe, over any field.
It applies the actual retract-image construction from `IdempotentImage`:
an idempotent fixes its smooth connected closed image and has a retraction
onto it. Conjugation equivariance makes the full pointwise image normal.
The defining normal-subgroup dichotomy for an almost-simple group makes that
image trivial or full, forcing the original endomorphism to be the trivial
map or the identity.

This adapter introduces no further hypotheses. The quantified test schemes
include nonreduced schemes. This is the field step of the Weil-factor
rigidity argument; the arbitrary-base rigidity statement requires further
product classification and gluing.
