# The intersection in the local opposite Borel construction

This internal auxiliary module is part of the proof of
`RelativeOppositeBorelStatement`. It extends the published affine-base dynamic
intersection formula in `Reductive.SteinbergBigCellGeometry` to an arbitrary
base when the centralizer has a supplied representative.

For an affine group scheme over any scheme, a cocharacter, and a monomorphic
homomorphism whose range is its centralizer, `Dynamic.parabolic_inf_opposite_eq_range`
identifies the intersection of the two opposite dynamic parabolics with that
range. The proof checks the upper inclusion on the affine open cover of the
base, using the published base-change formulas and affine intersection theorem.
The reverse inclusion follows directly from centralizer containment in both
dynamic parabolics. This lemma asserts no existence, Borel property or uniqueness.

`IsRepresentedBy.isClosedSubgroup_of_isClosedRepresentable` transports closedness
between two monomorphic representatives of the same all-test subgroup. The
representatives are isomorphic compatibly with their inclusions.

`exists_etaleLocal_oppositeBorel` assumes the full
`RelativeBorelDynamicPresentationStatement` as an explicit premise, together
with the original opposite Borel input data. It obtains the local negative
dynamic Borel from that premise. The published dynamic representability theorem
shows that its image has a closed representative, so the preceding transport
lemma makes the supplied negative Borel inclusion closed. The supplied torus is
a monomorphic representative of the centralizer, and the dynamic intersection
formula then gives the required all-test intersection equality on each member
of the étale cover. This proves only the local construction conditional on the
stated presentation premise; it discharges neither that premise nor the
matching, global descent or uniqueness obligations.
