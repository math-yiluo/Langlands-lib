# Restricting an external semidirect complement to the original group

This internal adapter works with the actual external semidirect group scheme.
For a supplied factorization `i ≫ a.semidirectInl = u`, membership in the range
of `i` is equivalent, on every scheme test, to membership in the range of `u`
after the normal-coordinate inclusion. Cancellation of that inclusion proves
the equivalence. Thus normality of the external range implies both normality
of the range in the original group and stability under the original action.

Suppose a commutative subgroup `j : M → a.semidirectProduct` and the supplied
external factor `u` have actual multiplication an isomorphism. Then
multiplication of `i` and the actual intersection of `M` with the normal
coordinate is also an isomorphism. The proof applies Yoneda on every scheme
test. Injectivity follows by mapping each pair to its external factor pair,
using injectivity of external multiplication, and cancelling the first
intersection projection. For surjectivity, decompose an original point in
the external product. The commutative-factor coordinate belongs to the normal
coordinate because it is the quotient of two normal-coordinate points.
The actual intersection pullback supplies its lift. The resulting pair maps
to the original point. No field, smoothness, connectedness, normality or torus
hypothesis is required for this restriction lemma.

Over a field, a unipotent subgroup of the external product projects trivially
to a split acting torus on every scheme test. The existing homomorphism
triviality theorem therefore puts its actual range inside the normal
coordinate. `semidirectNormalSubgroup` is the group-scheme factorization
through the monic normal inclusion, with the stated composite equality.

The results compose the published actual semidirect maps, scheme-theoretic
intersection and unipotent-to-torus triviality interfaces. They do not assert
existence of an external unipotent complement or prove the general solvable
ordered-product assertion.
