# A prescribed dynamic presentation over a connected base

This internal construction propagates a specified dynamic parabolic
presentation of a smooth geometrically connected affine subgroup from
one actual field fibre over a connected base scheme.

First, if a dynamic parabolic is the whole source group on one field
fibre, its monomorphic smooth affine representative is globally
isomorphic to the source by connected monomorphism rigidity. Thus the
parabolic is globally the whole source.

Given a closed subgroup inclusion `i : H → G` and a cocharacter of H,
assume that the actual field fibre of H equals the ambient dynamic
parabolic of the composed cocharacter. Closed-subgroup compatibility
makes the source parabolic full on that fibre, hence globally full.
Functoriality gives a global factorization of H through the ambient
parabolic representative. This factorization is monomorphic and is an
isomorphism on the specified fibre. Connected monomorphism rigidity
makes it a global isomorphism, retaining the inclusion equation.

`parabolicIsoOfFieldPresentation` chooses this actual isomorphism with
any supplied monomorphic representative of the ambient parabolic.
Its forward-map inclusion equation is proved, as is equality of the
original subgroup range with the full ambient dynamic parabolic.
All smoothness, affinity and geometric connectedness conditions are
retained explicitly. The base has no noetherian or reducedness condition.
