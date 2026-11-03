# Base change and fpqc descent of normalizers

This is internal infrastructure derived from the published definitions of subgroup
functors, their normalizers, and base change, together with the published fpqc
factorization-descent theorem. It is an auxiliary unit for parabolic
self-normalization; it does not prove that parabolic subgroups are self-normalizing.

For any base morphism `b : S' ⟶ S` and any subgroup functor `F` of a group scheme
`G`, its normalizer commutes with base change. No representability, affineness,
smoothness, finite-type, or field hypothesis is needed. Normalizers here are tested
after every refinement of every test scheme.

The construction `normalizerBaseChangeEquiv` is the multiplicative equivalence
between normalizer points of the base-changed subgroup over `U` and normalizer
points of the original subgroup over `U` regarded as an `S`-scheme. It is the
usual pullback point equivalence restricted to the two normalizer subgroups.

For forward containment, the proof transports conjugation and inverse
conjugation through the natural multiplicative pullback point equivalence. For
reverse containment, any refinement `V ⟶ U` over `S` gives `V` an `S'`-structure
by composition with the structural map of `U`. Its underlying `S`-scheme is
canonically isomorphic to the original `V`. The normalization hypothesis over
`S'` therefore tests this refinement too. Restricting back along the canonical
isomorphism gives both conjugation conditions on the original test scheme.

For a homomorphism `i : H ⟶ G` whose underlying morphism over `S` is a
monomorphism, self-normalization of its range is equivalent to
self-normalization after any quasi-compact, flat, surjective base change. The
reverse implication applies `le_range_of_baseChange_le` to the normalizer and
uses the elementary inclusion of a subgroup functor in its own normalizer.
All test schemes, including nonaffine and nonreduced schemes, are retained.
