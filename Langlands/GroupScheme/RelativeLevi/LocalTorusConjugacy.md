# Local Levi conjugacy from the relative torus statements

This internal construction works over every scheme `S` in every universe `u`.
It takes a reductive group scheme `G`, a relative parabolic inclusion
`i : P ⟶ G`, and two relative Levi inclusions `l : L ⟶ P` and
`l' : L' ⟶ P`, retaining their complete predicates.

The three entire propositions `EtaleLocalMaximalTorusExistenceStatement`,
`EtaleLocalMaximalTorusConjugacyStatement`, and `RelativeTorusLeviStatement`
are explicit inputs. The construction derives local ambient conjugators
without requiring supplied tori or a separate base-change stability premise.

`etaleLocallyRangeConjugate_of_one_maximalTorus` first assumes a maximal
torus of `P` contained in the range of `l`. It uses the local maximal-torus
construction for `l'` to obtain an actual étale cover. On each member it
assembles a maximal torus of the pulled-back `P` contained in the pulled-back
`l'`. The supplied torus of `l` pulls back to a maximal torus there.
Reductivity and relative parabolicity persist under base change; the full
relative Levi predicates persist under these étale maps. The supplied-torus
conjugacy theorem then gives conjugators on a further étale cover. The
pullback-point comparison projects these to conjugators over the original
base, preserving the predicate on every further test scheme. Composition
of covers gives the claimed single cover.

`etaleLocallyRangeConjugate_of_torusStatements` constructs a maximal torus
in `l` on another étale cover and repeats this procedure using the preceding
one-torus theorem. The resulting cover remains indexed in universe `u`;
composition uses dependent pairs of indices in that universe. The resulting
points lie in the ambient parabolic and satisfy `IsRangeConjugator`, which
tests subgroup membership after inverse conjugation on every relative test
scheme, including nonreduced schemes.

`relativeLeviConjugatorCover` chooses an actual resulting étale cover and,
on every member, an actual ambient conjugating point with that certificate.
This use of classical choice makes no canonicity claim.

The provenance is the composition of the local maximal-torus, supplied-torus
conjugacy, pullback-point, and cover-composition constructions. This module
does not prove the three supplied propositions, produce global points in
the unipotent radical, or prove `RelativeLeviConjugacyStatement`.
