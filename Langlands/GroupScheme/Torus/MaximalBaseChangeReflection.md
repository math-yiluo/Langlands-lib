# Reflection of maximal-torus maximality under field extension

Worker 1340.

This internal helper proves the reverse implication of maximal-torus
invariance for an inclusion already known to be closed over the original
field. It applies to any group scheme over a field and any extension in
the same universe. It does not require smoothness or affineness of the
ambient group.

`maximalTorusComparisonIsoOfBaseChange` constructs the actual original-field
isomorphism between `T.toGrp` and a competing closed torus `T'.toGrp`
when a specified comparison `f` factors the original inclusion and the
inclusion becomes maximal after extension. Its forward map is exactly
`f`, as recorded by `maximalTorusComparisonIsoOfBaseChange_hom`. This
construction uses the specified comparison map; it does not descend an
arbitrary isomorphism of the extended objects.

`IsMaximalTorus.of_baseChange hi h` assumes that the actual homomorphism
`i : T.toGrp ⟶ G` is closed and becomes a maximal torus after extending
the ground field from `k` to `K`. The torus predicate for `T` follows
from `IsTorus.of_baseChange`. Given any original-field competing closed
torus `i' : T'.toGrp ⟶ G` through which `i` factors, base change preserves
its torus predicate, its closedness and the factorization. Maximality
over `K` therefore makes the base change of the comparison map an
isomorphism. A field extension is fpqc, so `isoOfBaseChange` constructs
the original comparison isomorphism. Together with the original
closedness, these comparison isomorphisms prove maximality.

Closedness of `i` is an explicit input. This lemma neither proves
descent of closed immersions nor the forward implication of maximality
invariance, which must test competing tori over `K` that may not descend.
It does not prove the parabolic maximal-torus existence target.
