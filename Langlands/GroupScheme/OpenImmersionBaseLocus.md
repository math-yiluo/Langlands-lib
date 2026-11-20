# The base locus where a group monomorphism is an open immersion

`GroupMonomorphismOpenImmersionLocusStatement` concerns a group homomorphism
\(f\colon H\to N\) that is a monomorphism on the underlying schemes. Its
source is flat and locally of finite presentation over the base, and its
target is locally of finite type. The statement gives an open of the base
through which a test morphism factors exactly when the pullback of \(f\)
is an open immersion.

The open is the inverse image of the étale locus under the unit of \(H\).
For a test with image in this open, the pulled-back étale locus of \(f\)
contains the unit and is flat and surjective over the test. Translation by
the source group then propagates flatness to the entire pulled-back
homomorphism. Its local finite presentation and monomorphism give an open
immersion. In the other direction, for each test point the open immersion
gives a flat fibre map. Faithfully flat descent along the residue field
extension gives flatness on the original fibre. The fibrewise flatness
criterion applied at the unit, together with formal unramifiedness of the
monomorphism, gives membership in the étale locus.

This is the group-monomorphism case of the open condition used in
Raynaud's proof of SGA 3, Exposé XV, Lemma 5.5 (recomposed p. 268), which
cites Exposé VIB, Proposition 2.6. The Lean proof derives the condition
from the Library's stalkwise fibre criterion and the translation argument
for a flat family of group points.
