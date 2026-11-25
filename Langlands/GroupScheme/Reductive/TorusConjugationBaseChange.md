# Torus conjugation under arbitrary base change

This internal derived module concerns the all-test predicate `TorusConjugates`
from `IsogenyAdjointTorusDescent`. The supplied conjugating group is any
commutative group scheme; no torus, reductivity, isogeny or affineness
hypothesis is needed.

`torusConjugates_baseChange_iff` identifies conjugation for the canonical
pullbacks of the inclusion and both homomorphisms with conjugation for the
original homomorphisms. The parameter scheme over the new base is viewed over
the old base, and its point is projected by `baseChangePointsEquiv`.

The reverse implication lifts the desired equality through the injective
pullback-point equivalence and applies the original predicate. For the forward
implication, a test over the old base refining the parameter scheme acquires a
map to the new base through that parameter. Its pushforward is isomorphic to
the original test by the identity of underlying schemes. The proof lifts the
source-group point through the pullback-point equivalence, applies the new-base
predicate, projects its equality, uses naturality and the multiplication and
inverse laws, and cancels the test isomorphism. All scheme tests, including
nonreduced schemes, occur in this argument.

`torusConjugatorPointsEquiv` restricts the actual pullback-point equivalence to
the subtypes of points satisfying these predicates. Its inverse and inverse
laws are inherited from that equivalence.

`torusConjugates_torusIso_iff` changes the supplied commutative group by a group
scheme isomorphism and sends its point through the isomorphism. It follows by
expanding the predicate and associating compositions.

The provenance is the imported actual base-change point equivalence and its
naturality and homomorphism compatibility. The construction of the induced
test scheme follows the method already used for range conjugators in
`RelativeLevi.ConjugacyCovers`. No external literature or structural existence
result is used. This module does not assert existence of any conjugating point.
